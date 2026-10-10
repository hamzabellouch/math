import Mathlib
import OAI.MathematicalPhysics.BFSS.CliffordSymbols

namespace OAI

/-! Finite IMS identities and exact smooth cutoff energy decompositions. -/

namespace BFSSQuantum
noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)
lemma finite_ims_algebra {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ι → Fermion N)
    (y : Fermion N) (hb : ∑j, a j • b j = 0) :
    ∑j, ‖a j • y + b j‖ ^ 2 = (∑j, a j ^ 2) * ‖y‖ ^ 2 + ∑j, ‖b j‖ ^ 2 := by
  have hc : ∑j, a j * inner ℝ y (b j) = 0 := by
    simp_rw [← real_inner_smul_right]
    rw [← inner_sum, hb, inner_zero_right]
  simp only [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hd : ∑j, 2 * (a j * inner ℝ y (b j)) = 0 := by
    rw [← Finset.mul_sum, hc, mul_zero]
  simp only [hd, add_zero]

lemma cutoffGradient_partition {ι : Type*} [Fintype ι]
    (χ : ι → Boson N → ℝ)
    (hχ : ∀j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ j))
    (hpart : ∀x, ∑j, χ j x ^ 2 = 1) (x : Boson N) :
    ∑j, χ j x • cutoffGradient (χ j) x = 0 := by
  have hf : (fun y => ∑j, χ j y ^ 2) = fun _ => (1 : ℝ) := funext hpart
  have hd : fderiv ℝ (fun y => ∑j, χ j y ^ 2) x = 0 := by rw [hf]; simp
  rw [fderiv_fun_sum (A := fun j y => χ j y ^ 2)
    (fun j _ => ((hχ j).differentiable (by simp)).differentiableAt.pow 2)] at hd
  simp_rw [fderiv_fun_pow 2 ((hχ _).differentiable (by simp)).differentiableAt] at hd
  apply PiLp.ext
  intro p
  have hc := congrArg (fun L : Boson N →L[ℝ] ℝ => L (EuclideanSpace.single p 1)) hd
  simp only [sum_apply, IsSMulApply.smul_apply,
    zero_apply, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, smul_eq_mul] at hc
  have hc' : 2 * (∑j, χ j x * fderiv ℝ (χ j) x (EuclideanSpace.single p 1)) = 0 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc] using hc
  have hz : ∑j, χ j x * fderiv ℝ (χ j) x (EuclideanSpace.single p 1) = 0 := by linarith
  simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.zero_apply,
    cutoffGradient, smul_eq_mul] using hz

lemma charge_ims_pointwise {ι : Type*} [Fintype ι]
    (χ : ι → Boson N → ℝ)
    (hχ : ∀j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ j))
    (hpart : ∀x, ∑j, χ j x ^ 2 = 1) (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    ∑j, ‖M.charge α (realCutoff (χ j) (hχ j) f) x‖ ^ 2 =
      ‖M.charge α f x‖ ^ 2 +
        (1 / 2 : ℝ) * (∑j, ‖cutoffGradient (χ j) x‖ ^ 2) * ‖f x‖ ^ 2 := by
  let K : Boson N →ₗ[ℝ] Fermion N := {
    toFun ξ := (-Complex.I) • (M.principalSymbolLinear α ξ) (f x)
    map_add' ξ η := by simp only [map_add, IsAddApply.add_apply, smul_add]
    map_smul' r ξ := by
      simp only [map_smul, IsSMulApply.smul_apply, RingHom.id_apply]
      exact smul_comm (-Complex.I) r _
  }
  have hb : ∑j, χ j x • K (cutoffGradient (χ j) x) = 0 := by
    simp_rw [← map_smul K]
    rw [← map_sum]
    rw [cutoffGradient_partition χ hχ hpart x, map_zero]
  have hi := finite_ims_algebra (fun j => χ j x)
    (fun j => K (cutoffGradient (χ j) x)) (M.charge α f x) hb
  have hn (j : ι) : ‖K (cutoffGradient (χ j) x)‖ ^ 2 =
      (1 / 2 : ℝ) * ‖cutoffGradient (χ j) x‖ ^ 2 * ‖f x‖ ^ 2 := by
    change ‖(-Complex.I) • M.principalSymbol (Pi.single α 1) (cutoffGradient (χ j) x) (f x)‖ ^ 2 = _
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact M.principalSymbol_unit_norm_sq _ (basisSpinor_unit α) _ _
  have he (j : ι) : M.charge α (realCutoff (χ j) (hχ j) f) x =
      χ j x • M.charge α f x + K (cutoffGradient (χ j) x) := by
    rw [M.charge_realCutoff]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  simp_rw [he]
  rw [hi, hpart, one_mul]
  simp_rw [hn]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

lemma coreToL2_norm_sq (f : SmoothCore N) :
    ‖coreToL2 f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := congrArg Complex.re (coreToL2_inner f f)
  change RCLike.re (inner ℂ (coreToL2 f) (coreToL2 f)) =
    RCLike.re (∫ x, inner ℂ (f x) (f x)) at h
  rw [← integral_re (coreInner_integrable f f)] at h
  simpa only [inner_self_eq_norm_sq] using h

lemma coreNormSq_integrable (f : SmoothCore N) :
    Integrable (fun x => ‖f x‖ ^ 2) (volume : Measure (Boson N)) := by
  have h := (coreInner_integrable f f).re
  simpa only [← RCLike.re_to_complex, inner_self_eq_norm_sq] using h

lemma cutoffGradient_continuous (χ : Boson N → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    Continuous (cutoffGradient χ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : SpaceIndex × ColorIndex N => ℝ)).comp
  apply continuous_pi
  intro p
  exact hχ.continuous_fderiv (by simp) |>.clm_apply continuous_const

lemma cutoffError_integrable (χ : Boson N → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (f : SmoothCore N) :
    Integrable (fun x => ‖cutoffGradient χ x‖ ^ 2 * ‖f x‖ ^ 2)
      (volume : Measure (Boson N)) := by
  have hc : HasCompactSupport (fun x : Boson N => ‖f x‖ ^ 2) := by
    exact f.hasCompactSupport.comp_left (g := fun z : Fermion N => ‖z‖ ^ 2)
      (by simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
  have hp : HasCompactSupport (fun x : Boson N =>
      ‖cutoffGradient χ x‖ ^ 2 * ‖f x‖ ^ 2) :=
    hc.mul_left (f := fun x => ‖cutoffGradient χ x‖ ^ 2)
  exact (((cutoffGradient_continuous χ hχ).norm.pow 2).mul
    (f.continuous.norm.pow 2)).integrable_of_hasCompactSupport hp

lemma charge_ims {ι : Type*} [Fintype ι]
    (χ : ι → Boson N → ℝ)
    (hχ : ∀j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ j))
    (hpart : ∀x, ∑j, χ j x ^ 2 = 1) (α : SpinIndex) (f : SmoothCore N) :
    ∑j, ‖coreToL2 (M.charge α (realCutoff (χ j) (hχ j) f))‖ ^ 2 =
      ‖coreToL2 (M.charge α f)‖ ^ 2 + (1 / 2 : ℝ) *
        ∑j, ∫ x, ‖cutoffGradient (χ j) x‖ ^ 2 * ‖f x‖ ^ 2 := by
  simp_rw [coreToL2_norm_sq]
  rw [← integral_finsetSum _ (fun j _ => coreNormSq_integrable _)]
  simp_rw [M.charge_ims_pointwise χ hχ hpart α f]
  have hg : Integrable (fun x => ∑j, ‖cutoffGradient (χ j) x‖ ^ 2 * ‖f x‖ ^ 2)
      (volume : Measure (Boson N)) :=
    integrable_finsetSum _ (fun j _ => cutoffError_integrable (χ j) (hχ j) f)
  simp only [mul_assoc, Finset.sum_mul]
  rw [integral_add (coreNormSq_integrable _) (hg.const_mul (1/2))]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    cutoffError_integrable (χ j) (hχ j) f)]

lemma coreForm_ims {ι : Type*} [Fintype ι]
    (χ : ι → Boson N → ℝ)
    (hχ : ∀j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ j))
    (hpart : ∀x, ∑j, χ j x ^ 2 = 1) (f : SmoothCore N) :
    ∑j, M.coreForm (realCutoff (χ j) (hχ j) f) =
      M.coreForm f + (1 / 2 : ℝ) *
        ∑j, ∫ x, ‖cutoffGradient (χ j) x‖ ^ 2 * ‖f x‖ ^ 2 := by
  unfold coreForm
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [M.charge_ims χ hχ hpart]
  rw [Finset.sum_add_distrib, mul_add]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end AlgebraData
end
end BFSSQuantum

end OAI
