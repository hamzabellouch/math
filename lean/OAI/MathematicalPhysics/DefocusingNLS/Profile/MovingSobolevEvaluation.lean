import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalCharacter
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevEvaluationContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.MovingEvaluationDerivative

namespace OAI

/-! # Differentiating Sobolev Fourier series along the physical dilation -/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def sobolevPhysicalDirectional (k : ℝ) (f : FourierL2) (x v : E) : ℂ :=
  ∑' n : frequencyLattice, sobolevFourierCoefficient k f n *
    ((⟪v, (n : E)⟫ : ℝ) : ℂ) * Complex.I * spatialFourierCharacter n x

theorem hasDerivAt_sobolev_physical_ray (k : ℝ) (hk : 8 < k)
    (f : FourierL2) (y : E) (t : ℝ) :
    HasDerivAt (fun s => sobolevTorusFunction k f (euclideanToTorus (s • y)))
      (sobolevPhysicalDirectional k f (t • y) y) t := by
  let g := fun (n : frequencyLattice) (s : ℝ) =>
    sobolevFourierCoefficient k f n * spatialFourierCharacter n (s • y)
  let g' := fun (n : frequencyLattice) (s : ℝ) =>
    sobolevFourierCoefficient k f n * ((⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I *
      spatialFourierCharacter n (s • y)
  have hd (n : frequencyLattice) (s : ℝ) : HasDerivAt (g n) (g' n s) s := by
    have h := ((((hasDerivAt_id s).mul_const ⟪y, (n : E)⟫).ofReal_comp.mul_const
      Complex.I).cexp).const_mul (sobolevFourierCoefficient k f n)
    simp only [id_eq, one_mul] at h
    simp only [g, g', spatialFourierCharacter, real_inner_smul_left]
    convert h using 1
    ring
  have hb (n : frequencyLattice) (s : ℝ) :
      ‖g' n s‖ ≤ (‖y‖ * (1 + ‖n‖ ^ 2)) * ‖sobolevFourierCoefficient k f n‖ := by
    have hn : ‖n‖ ≤ 1 + ‖n‖ ^ 2 := by nlinarith [sq_nonneg (‖n‖ - 1)]
    simp only [g', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, spatialFourierCharacter_norm]
    calc
      _ ≤ ‖sobolevFourierCoefficient k f n‖ * (‖y‖ * ‖n‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm y (n : E)) (norm_nonneg _)
      _ ≤ _ := by
        calc
          _ ≤ ‖sobolevFourierCoefficient k f n‖ * (‖y‖ * (1 + ‖n‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hn (norm_nonneg y)) (norm_nonneg _)
          _ = _ := by ring
  have hs : Summable (fun n : frequencyLattice =>
      (‖y‖ * (1 + ‖n‖ ^ 2)) * ‖sobolevFourierCoefficient k f n‖) := by
    simpa only [mul_assoc] using (summable_derivative_bound k hk f).mul_left ‖y‖
  have h0 : Summable (fun n => g n (0 : ℝ)) := by
    apply (summable_norm_sobolevFourierCoefficient k (by linarith) f).of_norm_bounded
    intro n
    simp only [g, norm_mul, spatialFourierCharacter_norm, mul_one, le_refl]
  have h := hasDerivAt_tsum hs hd hb h0 t
  convert h using 1
  · funext s
    rw [sobolevTorusFunction_apply k (by linarith)]
    have he := (hasSum_sobolevPointEvaluation k (by linarith)
      (euclideanToTorus (s • y)) f).tsum_eq
    simpa only [torusCharacter_euclidean] using he.symm
  · rfl

theorem hasDerivAt_sobolev_expanding_point (k L : ℝ) (hk : 8 < k)
    (f : FourierL2) (y : E) (t : ℝ) :
    HasDerivAt
      (fun s => sobolevTorusFunction k f (euclideanToTorus ((expandingRadius L s)⁻¹ • y)))
      ((-((expandingRadius L t)⁻¹) / 2) •
        sobolevPhysicalDirectional k f ((expandingRadius L t)⁻¹ • y) y) t := by
  exact (hasDerivAt_sobolev_physical_ray k hk f y _).scomp t
    (hasDerivAt_expandingRadius_inv L t)

end DefocusingNLS

end OAI
