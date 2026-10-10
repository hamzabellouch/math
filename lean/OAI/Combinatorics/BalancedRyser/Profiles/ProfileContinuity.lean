import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCompactness

namespace OAI

open Filter
open scoped Topology Classical

namespace Balanced.ProfileContinuity

theorem summable_mul_of_abs_le_one
    {ι : Type*} {p w : ι → ℝ} (hp : Summable p)
    (hw : ∀ i, |w i| ≤ 1) : Summable (fun i => p i * w i) := by
  apply hp.abs.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem abs_tsum_mul_sub_le_tsum_abs
    {ι : Type*} {p q w : ι → ℝ} (hp : Summable p) (hq : Summable q)
    (hw : ∀ i, |w i| ≤ 1) :
    |(∑' i, p i * w i) - ∑' i, q i * w i| ≤ ∑' i, |p i - q i| := by
  have hsub := summable_mul_of_abs_le_one (hp.sub hq) hw
  have hsubNorm : Summable (fun i => ‖(p i - q i) * w i‖) := by
    simpa only [Real.norm_eq_abs] using hsub.abs
  rw [← (summable_mul_of_abs_le_one hp hw).tsum_sub
    (summable_mul_of_abs_le_one hq hw)]
  simp_rw [← sub_mul]
  calc
    |∑' i, (p i - q i) * w i| ≤ ∑' i, ‖(p i - q i) * w i‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsubNorm
    _ ≤ ∑' i, |p i - q i| := by
      apply Summable.tsum_le_tsum _ hsubNorm (hp.sub hq).abs
      intro i
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem tendsto_tsum_mul_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    {w : α → ι → ℝ} {v : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (hweight : ∀ i, Tendsto (fun n => w n i) l (𝓝 (v i)))
    (hbound : ∀ n i, |w n i| ≤ 1) :
    Tendsto (fun n => ∑' i, p n i * w n i) l (𝓝 (∑' i, q i * v i)) := by
  have hfixed : Tendsto (fun n => ∑' i, q i * w n i)
      l (𝓝 (∑' i, q i * v i)) := by
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      exact (hweight i).const_mul (q i)
    · exact Eventually.of_forall fun n i => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg i)]
        exact (mul_le_mul_of_nonneg_left (hbound n i) (hq_nonneg i)).trans_eq (mul_one _)
  have hdiff : Tendsto (fun n => (∑' i, p n i * w n i) - ∑' i, q i * w n i)
      l (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => ?_) (tendsto_tsum_abs_sub_of_probability_mass
        hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
    simpa only [Real.norm_eq_abs] using
      abs_tsum_mul_sub_le_tsum_abs (hp_sum n).summable hq_sum.summable (hbound n)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed

theorem continuous_tsum_mul_of_probability_mass
    {ι X : Type*} [TopologicalSpace X] {p w : X → ι → ℝ}
    (hp_nonneg : ∀ x i, 0 ≤ p x i) (hp_sum : ∀ x, HasSum (p x) 1)
    (hp_cont : ∀ i, Continuous (fun x => p x i))
    (hw_cont : ∀ i, Continuous (fun x => w x i))
    (hw_bound : ∀ x i, |w x i| ≤ 1) :
    Continuous (fun x => ∑' i, p x i * w x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact tendsto_tsum_mul_of_probability_mass hp_nonneg (hp_nonneg x)
    hp_sum (hp_sum x) (fun i => (hp_cont i).continuousAt)
    (fun i => (hw_cont i).continuousAt) hw_bound

theorem continuous_profile_bounded_test_sum
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    {w : Set.Icc (0 : ℝ) 1 → ι → ℝ}
    (hw_cont : ∀ i, Continuous (fun z => w z i))
    (hw_bound : ∀ z i, |w z i| ≤ 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * w x.2 i) := by
  apply continuous_tsum_mul_of_probability_mass
  · intro x i
    exact hp_nonneg x.1.val x.1.property i
  · intro x
    exact hp_sum x.1.val x.1.property
  · intro i
    exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  · intro i
    exact (hw_cont i).comp continuous_snd
  · intro x i
    exact hw_bound x.2 i

theorem continuous_profile_power_series
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * x.2.val ^ (rate i)) := by
  apply continuous_profile_bounded_test_sum hp_nonneg hp_sum
    (w := fun z i => z.val ^ (rate i))
  · intro i
    exact (Real.continuous_rpow_const (hrate i)).comp continuous_subtype_val
  · intro z i
    rw [abs_of_nonneg (Real.rpow_nonneg z.property.1 _)]
    exact Real.rpow_le_one z.property.1 z.property.2 (hrate i)

theorem continuous_profile_selected_power_series
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    (active : Set ι) (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * (if i ∈ active then x.2.val ^ (rate i) else 0)) := by
  classical
  apply continuous_profile_bounded_test_sum hp_nonneg hp_sum
    (w := fun z i => if i ∈ active then z.val ^ (rate i) else 0)
  · intro i
    by_cases hi : i ∈ active
    · simp only [ite_eq_left hi]
      exact (Real.continuous_rpow_const (hrate i)).comp continuous_subtype_val
    · simp only [ite_eq_right hi]
      exact continuous_const
  · intro z i
    split_ifs with hi
    · rw [abs_of_nonneg (Real.rpow_nonneg z.property.1 _)]
      exact Real.rpow_le_one z.property.1 z.property.2 (hrate i)
    · norm_num

theorem continuous_plane_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * x.2.val ^ ((ij.1 : ℝ) + Real.sqrt 2 * ij.2)) := by
  apply continuous_profile_power_series hp_nonneg hp_sum
  intro ij
  positivity

theorem continuous_deletion_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * (if ij.1 ≠ 0 then
        x.2.val ^ (((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2) else 0)) := by
  have h := continuous_profile_selected_power_series hp_nonneg hp_sum
    {ij | ij.1 ≠ 0} (fun ij => ((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2)
    (fun ij => by positivity)
  convert h using 1
  funext x
  apply tsum_congr
  intro ij
  by_cases hi : ij.1 = 0 <;> simp [hi]

theorem continuous_cover_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * (if ij.2 ≠ 0 then
        x.2.val ^ ((ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ)) else 0)) := by
  have h := continuous_profile_selected_power_series hp_nonneg hp_sum
    {ij | ij.2 ≠ 0} (fun ij => (ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ))
    (fun ij => by positivity)
  convert h using 1
  funext x
  apply tsum_congr
  intro ij
  by_cases hi : ij.2 = 0 <;> simp [hi]

end Balanced.ProfileContinuity

end OAI
