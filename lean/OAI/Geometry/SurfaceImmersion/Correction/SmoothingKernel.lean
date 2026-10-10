import OAI.Geometry.SurfaceImmersion.Correction.SmoothingMoments
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-! Smooth compactly supported smoothing kernels with arbitrarily many
vanishing moments, constructed from finitely many positive dilations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma continuous_monomial (α : Fin 2 → ℕ) : Continuous (monomial α) := by
  unfold monomial
  fun_prop

lemma smooth_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K) (a : ℝ) :
    ContDiff ℝ ∞ (dilate K a) :=
  contDiff_const.mul (hK.comp (contDiff_id.const_smul a⁻¹))

lemma compact_dilate {K : Base → ℝ} (hK : HasCompactSupport K) {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (dilate K a) := by
  let e : Base ≃ₜ Base := Homeomorph.smul (Units.mk0 a⁻¹ (inv_ne_zero ha))
  have h := (hK.comp_homeomorph e).mul_left (f := fun _ => (a ^ 2)⁻¹)
  exact h

lemma integrable_moment_dilate {K : Base → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (α : Fin 2 → ℕ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun x => monomial α x * dilate K a x) := by
  have hd : Continuous (dilate K a) :=
    continuous_const.mul (hK.comp (continuous_id.const_smul a⁻¹))
  exact ((continuous_monomial α).mul hd).integrable_of_hasCompactSupport
    (compact_dilate hKc ha).mul_left

lemma moment_sum_dilates {r : ℕ} {K : Base → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (b c : Fin (r + 1) → ℝ) (hb : ∀ i, 0 < b i) (α : Fin 2 → ℕ) :
    (∫ x, monomial α x * (∑ i, c i * dilate K (b i) x)) =
      (∑ i, c i * b i ^ degree α) * ∫ x, monomial α x * K x := by
  have hi (i : Fin (r + 1)) : Integrable (fun x => c i * (monomial α x * dilate K (b i) x)) :=
    (integrable_moment_dilate hK hKc α (hb i).ne').const_mul (c i)
  have heq : (fun x => monomial α x * (∑ i, c i * dilate K (b i) x)) =
      (fun x => ∑ i, c i * (monomial α x * dilate K (b i) x)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul, moment_dilate K α (hb _)]
  simp only [← mul_assoc, ← Finset.sum_mul]

def basicBump : ContDiffBump (0 : Base) := ⟨1, 2, by norm_num, by norm_num⟩

def basicKernel : Base → ℝ := basicBump.normed volume

lemma smooth_basicKernel : ContDiff ℝ ∞ basicKernel := basicBump.contDiff_normed

lemma compact_basicKernel : HasCompactSupport basicKernel := basicBump.hasCompactSupport_normed

lemma integral_basicKernel : (∫ x, basicKernel x) = 1 := basicBump.integral_normed

/-- A concrete kernel used for finite-order smoothing. Its mass is one and
all nonconstant coordinate moments through degree `r` vanish. -/
theorem exists_smoothing_kernel (r : ℕ) :
    ∃ K : Base → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧
      (∫ x, K x) = 1 ∧ ∀ α : Fin 2 → ℕ, 1 ≤ degree α → degree α ≤ r →
        (∫ x, monomial α x * K x) = 0 := by
  let f : Base → ℝ := basicKernel
  have hfs : ContDiff ℝ ∞ f := smooth_basicKernel
  have hfc : HasCompactSupport f := compact_basicKernel
  have hfi : (∫ x, f x) = 1 := integral_basicKernel
  let b : Fin (r + 1) → ℝ := fun i => ((i.val + 1 : ℕ) : ℝ)
  have hb (i : Fin (r + 1)) : 0 < b i := by dsimp [b]; positivity
  obtain ⟨c, hc⟩ := exists_positive_dilation_weights r
  let K : Base → ℝ := fun x => ∑ i, c i * dilate f (b i) x
  have hs : ContDiff ℝ ∞ K := ContDiff.sum (fun i _ => (contDiff_const (c := c i)).mul (smooth_dilate hfs (b i)))
  have hk : HasCompactSupport K := by
    have hh := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i x => c i * dilate f (b i) x)
      (fun i _ => (compact_dilate hfc (hb i).ne').mul_left)
    have heq : (∑ i, fun x => c i * dilate f (b i) x) = K := by
      funext x
      simp only [K, Finset.sum_apply]
    exact heq ▸ hh
  refine ⟨K, hs, hk, ?_, ?_⟩
  · let α : Fin 2 → ℕ := fun _ => 0
    have hm := moment_sum_dilates hfs.continuous hfc b c hb α
    have hm' : (∫ x, K x) = (∑ i, c i) * ∫ x, f x := by
      simpa only [α, degree, Finset.sum_const_zero, monomial, pow_zero,
        Finset.prod_const_one, one_mul, mul_one] using hm
    rw [hfi, mul_one] at hm'
    exact hm'.trans (by simpa using hc 0)
  · intro α hα hαr
    have hm := moment_sum_dilates hfs.continuous hfc b c hb α
    let j : Fin (r + 1) := ⟨degree α, by omega⟩
    have hj : j ≠ 0 := by intro he; have := congrArg Fin.val he; dsimp [j] at this; omega
    have hcancel := hc j
    simp only [ite_eq_right_iff.mpr (fun h => (hj h).elim)] at hcancel
    have heq : (∑ i, c i * b i ^ degree α) = 0 := hcancel
    exact hm.trans (by rw [heq, zero_mul])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
