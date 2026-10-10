import Mathlib
import OAI.Geometry.Borsuk.Projectors.Basic

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}

noncomputable def homogeneousLift (f : V → ι → ℝ) (v : V) : ι → ℝ :=
  fun i => ‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i

@[simp] lemma homogeneousLift_zero (f : V → ι → ℝ) : homogeneousLift f 0 = 0 := by
  ext i
  simp [homogeneousLift]

lemma homogeneousLift_unit (f : V → ι → ℝ) {v : V} (hv : ‖v‖ = 1) :
    homogeneousLift f v = f v := by
  ext i
  simp [homogeneousLift, hv]

variable [Fintype ι]

lemma Admissible.lift_nonneg {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    0 ≤ homogeneousLift f v i := by
  by_cases hv : v = 0
  · simp [hv]
  · exact mul_nonneg (sq_nonneg _) (hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i)

lemma Admissible.lift_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, homogeneousLift f v i = ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · simp only [homogeneousLift, ← Finset.mul_sum]
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    rw [hf.sum_one _ hn, mul_one]

lemma Admissible.lift_abs_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, |homogeneousLift f v i| = ‖v‖ ^ 2 := by
  simp only [abs_of_nonneg (hf.lift_nonneg v _), hf.lift_sum]

lemma Admissible.lift_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    homogeneousLift f v i ≤ ‖v‖ ^ 2 := by
  classical
  rw [← hf.lift_sum v]
  exact Finset.single_le_sum (fun j _ => hf.lift_nonneg v j) (Finset.mem_univ i)

lemma Admissible.lift_norm_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ‖homogeneousLift f v‖ ≤ ‖v‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.lift_nonneg v i)] using hf.lift_le v i

lemma Admissible.lift_even {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    homogeneousLift f (-v) = homogeneousLift f v := by
  ext i
  simp [homogeneousLift, smul_neg, hf.antipodal]

omit [Fintype ι] in
lemma homogeneousLift_smul_pos (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  ext i
  have he : (‖t • v‖⁻¹ : ℝ) • (t • v) = (‖v‖⁻¹ : ℝ) • v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
    congr 1
    field_simp
  change ‖t • v‖ ^ 2 * f ((‖t • v‖⁻¹ : ℝ) • (t • v)) i = t ^ 2 * (‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  ring

omit [Fintype ι] in
lemma homogeneousLift_smul_nonneg (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  · exact homogeneousLift_smul_pos f v hp

lemma Admissible.lift_continuous {f : V → ι → ℝ} (hf : Admissible f) :
    Continuous (homogeneousLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, homogeneousLift_zero]
    apply squeeze_zero_norm (fun x => hf.lift_norm_le x)
    have hc : Continuous (fun x : V => ‖x‖ ^ 2) := continuous_norm.pow 2
    simpa using hc.tendsto (0 : V)
  · have hn : ContinuousAt (fun x : V => (‖x‖⁻¹ : ℝ) • x) v :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_norm.continuousAt.pow 2).mul ((hf.smooth i).continuous.continuousAt.comp hn)

lemma Admissible.lift_orthogonal {f : V → ι → ℝ} (hf : Admissible f)
    {u v : V} (huv : ⟪u, v⟫ = 0) (i : ι) :
    homogeneousLift f u i * homogeneousLift f v i = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hn : ⟪(‖u‖⁻¹ : ℝ) • u, (‖v‖⁻¹ : ℝ) • v⟫ = 0 := by
    simp [inner_smul_left, inner_smul_right, huv]
  have h := hf.orthogonal _ _ (norm_smul_inv_norm (𝕜 := ℝ) hu) (norm_smul_inv_norm (𝕜 := ℝ) hv) hn i
  have hnu := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hu) i
  have hnv := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i
  have hz : f ((‖u‖⁻¹ : ℝ) • u) i = 0 ∨ f ((‖v‖⁻¹ : ℝ) • v) i = 0 := by
    by_contra hh
    push Not at hh
    exact h ⟨lt_of_le_of_ne hnu (Ne.symm hh.1), lt_of_le_of_ne hnv (Ne.symm hh.2)⟩
  rcases hz with hz | hz <;> simp [homogeneousLift, hz]
end HomogeneousLift

open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

end BorsukNine

end OAI
