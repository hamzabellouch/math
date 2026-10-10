import OAI.Analysis.KLS.Spectral.BrascampLieb
import OAI.Analysis.KLS.Regularization.RegularPotential

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

theorem quadratic_inverse_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hlower : ∀ v : ι → ℝ, t * (v ⬝ᵥ v) ≤ v ⬝ᵥ H *ᵥ v) (g : ι → ℝ) :
    t * (g ⬝ᵥ H⁻¹ *ᵥ g) ≤ g ⬝ᵥ g := by
  let v := H⁻¹ *ᵥ g
  have hmul : H *ᵥ v = g := by
    rw [show v = H⁻¹ *ᵥ g from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mulVec]
  have hl : t * (v ⬝ᵥ v) ≤ g ⬝ᵥ v := by
    simpa only [hmul, dotProduct_comm v g] using hlower v
  have hsq : 0 ≤ (g - t • v) ⬝ᵥ (g - t • v) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg ((g - t • v) i)
  have heq : (g - t • v) ⬝ᵥ (g - t • v) =
      g ⬝ᵥ g - 2 * t * (g ⬝ᵥ v) + t ^ 2 * (v ⬝ᵥ v) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm v g]
    ring
  rw [heq] at hsq
  change t * (g ⬝ᵥ v) ≤ g ⬝ᵥ g
  nlinarith [mul_le_mul_of_nonneg_left hl ht]

theorem IsRegularPotential.hessianMatrix_posDef {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) : (hessianMatrix V x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hessianMatrix_isSymm
      ((hV.contDiff.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 2 V).contDiffAt)).eq
  · intro v hv
    let w : Space n := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro heq
      apply hv
      funext i
      exact congrArg (fun u : Space n => u i) heq
    simpa only [second_fderiv_eq_hessianMatrix, w, PiLp.toLp_apply, star_trivial] using
      hV.hessian_pos x hw

theorem IsRegularPotential.steinGamma_self_le {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (h : Space n → ℝ) (x : Space n) :
    t * steinGamma V h h x ≤ ‖gradient h x‖ ^ 2 := by
  have hlower : ∀ v : Fin n → ℝ,
      t * (v ⬝ᵥ v) ≤ v ⬝ᵥ hessianMatrix V x *ᵥ v := by
    intro v
    have hv := hV.lower_bound x (WithLp.toLp 2 v)
    rw [EuclideanSpace.real_norm_sq_eq] at hv
    simpa only [second_fderiv_eq_hessianMatrix,
      PiLp.toLp_apply, dotProduct, pow_two] using hv
  have hb := quadratic_inverse_upper_bound (hV.hessianMatrix_posDef x) hV.lower_pos.le
    hlower (fun i => gradient h x i)
  rw [steinGamma_self_eq_dotProduct, EuclideanSpace.real_norm_sq_eq]
  simpa only [dotProduct, pow_two] using hb

theorem IsRegularPotential.poincare {n : ℕ} {V f : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t')
    (hVint : Integrable (fun x => Real.exp (-V x))) (hf : IsTestFunction f) :
    t * variance (potentialMeasure V) f ≤ dirichletEnergy (potentialMeasure V) f := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hqint : Integrable (steinGamma V f f) (potentialMeasure V) :=
    (contDiff_steinGamma_self hV.contDiff hf.1 hV.hessianMatrix_posDef).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_steinGamma_self V hf)
  calc
    t * variance (potentialMeasure V) f ≤
        t * (∫ x, steinGamma V f f x ∂potentialMeasure V) :=
      mul_le_mul_of_nonneg_left
        (brascamp_lieb hV.contDiff hVint hV.hessianMatrix_posDef hf) hV.lower_pos.le
    _ = ∫ x, t * steinGamma V f f x ∂potentialMeasure V := (integral_const_mul _ _).symm
    _ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure V :=
      integral_mono (hqint.const_mul t) (hf.integrable_gradient_sq _) (hV.steinGamma_self_le f)
    _ = dirichletEnergy (potentialMeasure V) f := rfl

end LeanBlast.KLS

end

end OAI
