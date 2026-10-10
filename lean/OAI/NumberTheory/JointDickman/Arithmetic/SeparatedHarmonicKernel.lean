import OAI.NumberTheory.JointDickman.Analysis.MellinSampleDuality
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OAI

/-! # Harmonic-decay kernels on separated samples -/
namespace JointDickman
open Finset
open scoped Classical

private lemma interval_sample_card (S : Finset ℝ) (x : ℝ → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) (b : ℝ) :
    (S.filter (fun i => b ≤ x i ∧ x i < b+1)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS,hi⟩ := mem_filter.mp hi
  obtain ⟨hjS,hj⟩ := mem_filter.mp hj
  by_contra hne
  have hh := hsep i hiS j hjS hne
  have ht : |x i-x j| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

private lemma absolute_sample_card (S : Finset ℝ) (x : ℝ → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) (b : ℝ) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b+1)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b+1)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b+1)
  have hp : P.card ≤ 1 := interval_sample_card S x hsep b
  have hq : Q.card ≤ 1 := interval_sample_card S (fun i => -x i)
    (by intro i hi j hj hne; simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hne) b
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b+1) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS,hi⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · exact mem_union_left Q (mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hi⟩)
    · exact mem_union_right P (mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hi⟩)
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

/-- Harmonic row sums grow only logarithmically with the diameter of the
sample set. The proof uses at most two points in each absolute unit band. -/
theorem separated_harmonic_kernel_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (t T : ℝ) (hT : 0 ≤ T) (hdiam : ∀ u ∈ S, |t-u| ≤ T) :
    (∑ u ∈ S, 1/(1+|t-u|)) ≤ 2*(1+Real.log (T+1)) := by
  let b : ℝ → ℕ := fun u => ⌊|t-u|⌋₊
  let K := ⌊T⌋₊
  let F : ℕ → Finset ℝ := fun j => S.filter (fun u => b u=j)
  have hpart : (∑ u ∈ S, 1/(1+|t-u|)) =
      ∑ j ∈ range (K+1), ∑ u ∈ F j, 1/(1+|t-u|) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro u hu
    apply mem_range.mpr
    have hh : b u ≤ K := Nat.floor_le_floor (hdiam u hu)
    omega
  have hband (j : ℕ) (u : ℝ) (hu : u ∈ F j) :
      (j:ℝ) ≤ |t-u| ∧ |t-u| < (j:ℝ)+1 := by
    have he := (mem_filter.mp hu).2
    have hl := Nat.floor_le (abs_nonneg (t-u))
    have hh := Nat.lt_floor_add_one |t-u|
    change (b u:ℝ) ≤ |t-u| at hl
    change |t-u| < (b u:ℝ)+1 at hh
    rw [he] at hl hh
    exact ⟨hl,hh⟩
  have hc (j : ℕ) : (F j).card ≤ 2 := by
    apply (card_le_card (s := F j) (t := S.filter
      (fun u => (j:ℝ) ≤ |t-u| ∧ |t-u| < (j:ℝ)+1)) ?_).trans
      (absolute_sample_card S (fun u => t-u)
        (by intro u hu v hv hne; simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep u hu v hv hne) j)
    intro u hu
    exact mem_filter.mpr ⟨(mem_filter.mp hu).1,hband j u hu⟩
  have hj (j : ℕ) : (∑ u ∈ F j, 1/(1+|t-u|)) ≤ 2/(1+(j:ℝ)) := by
    calc
      _ ≤ ∑ _u ∈ F j, 1/(1+(j:ℝ)) := sum_le_sum fun u hu =>
        one_div_le_one_div_of_le (by positivity) (by linarith [(hband j u hu).1])
      _ = ((F j).card:ℝ)/(1+(j:ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hc j) (by positivity)
  rw [hpart]
  apply (sum_le_sum fun j _ => hj j).trans
  have he : (∑ j ∈ range (K+1), 2/(1+(j:ℝ))) = 2*(harmonic (K+1):ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one,
      Rat.cast_natCast, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [add_comm]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (harmonic_le_one_add_log (K+1)).trans
  have hk : ((K+1:ℕ):ℝ) ≤ T+1 := by
    push_cast
    exact add_le_add (Nat.floor_le hT) le_rfl
  gcongr

end JointDickman

end OAI
