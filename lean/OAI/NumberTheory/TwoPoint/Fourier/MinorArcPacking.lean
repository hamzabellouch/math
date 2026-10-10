import OAI.NumberTheory.TwoPoint.Fourier.MinorArcRationalSpacing

namespace OAI

/-! Elementary interval packing for separated phase representatives. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_interval_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ x i ∧ x i < b + δ)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS, hix⟩ := mem_filter.mp hi
  obtain ⟨hjS, hjx⟩ := mem_filter.mp hj
  by_contra hij
  have hh := hsep i hiS j hjS hij
  have habs : |x i - x j| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma minor_arc_absolute_band_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b + δ)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b + δ)
  have hP : P.card ≤ 1 := minor_arc_interval_packing S x δ b hsep
  have hQ : Q.card ≤ 1 := by
    apply minor_arc_interval_packing S (fun i => -x i) δ b
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS, hix⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · apply mem_union_left
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hix⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hix⟩
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

end TwoPointCorrelations

end OAI
