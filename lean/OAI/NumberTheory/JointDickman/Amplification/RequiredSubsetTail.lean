import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCountChernoff

namespace OAI

/-! # Prescribed inclusions with a remaining prefix-count restriction -/

namespace JointDickman
open Finset Classical

/-- Conditioning on prescribed independent inclusions leaves the other
parameters unchanged. The test remains inside the finite expectation. -/
theorem bernoulliSubsetMass_required_test (P A : Finset ℕ) (q : ℕ → ℝ)
    (hA : A ⊆ P) (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S*F S else 0) =
      (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset,
        bernoulliSubsetMass (P \ A) q R*F (A ∪ R) := by
  rw [← sum_filter,mul_sum]
  apply sum_bij (fun S _ => S \ A)
  · intro S hS
    exact mem_powerset.mpr (sdiff_subset_sdiff
      (mem_powerset.mp (mem_filter.mp hS).1) subset_rfl)
  · intro S hS T hT he
    have hs := sdiff_union_of_subset (mem_filter.mp hS).2
    have ht := sdiff_union_of_subset (mem_filter.mp hT).2
    rw [he] at hs
    exact hs.symm.trans ht
  · intro R hR
    have hr := mem_powerset.mp hR
    refine ⟨A ∪ R,mem_filter.mpr ⟨mem_powerset.mpr
      (union_subset hA (hr.trans sdiff_subset)),subset_union_left⟩,?_⟩
    ext p
    have hp : p ∈ R → p ∉ A := fun h => (mem_sdiff.mp (hr h)).2
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  · intro S hS
    have has := (mem_filter.mp hS).2
    have he : (P \ A) \ (S \ A) = P \ S := by
      ext p
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hp,ha⟩,hs⟩
        exact ⟨hp,fun h => hs ⟨h,ha⟩⟩
      · rintro ⟨hp,hs⟩
        exact ⟨⟨hp,fun h => hs (has h)⟩,fun h => hs h.1⟩
    have hu : A ∪ (S \ A) = S := union_sdiff_of_subset has
    rw [hu]
    unfold bernoulliSubsetMass
    rw [he,← prod_sdiff has]
    ring

/-- Lower-tail Chernoff bound with the prescribed inclusions retained.
This is the finite estimate used for numeric additions in `moments.tex`. -/
theorem bernoulliSubsetMass_required_prefix_tail (P A Q : Finset ℕ) (q : ℕ → ℝ)
    (hA : A ⊆ P) (hAQ : A ⊆ Q) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∑ S ∈ P.powerset, if A ⊆ S ∧ ((S ∩ Q).card : ℝ) ≤ r then
      bernoulliSubsetMass P q S else 0) ≤
      (∏ p ∈ A, q p)*Real.exp (t*(r-A.card)+
        (Real.exp (-t)-1)*∑ p ∈ (P \ A) ∩ Q, q p) := by
  have he : (∑ S ∈ P.powerset, if A ⊆ S ∧ ((S ∩ Q).card : ℝ) ≤ r then
      bernoulliSubsetMass P q S else 0) =
      (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset,
        if ((R ∩ Q).card : ℝ) ≤ r-A.card then bernoulliSubsetMass (P \ A) q R else 0 := by
    calc
      _ = ∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S*
          (if ((S ∩ Q).card : ℝ) ≤ r then 1 else 0) else 0 := by
        apply sum_congr rfl
        intro S _
        split_ifs <;> simp_all
      _ = (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset, bernoulliSubsetMass (P \ A) q R*
          (if (((A ∪ R) ∩ Q).card : ℝ) ≤ r then 1 else 0) :=
        bernoulliSubsetMass_required_test P A q hA _
      _ = _ := by
        congr 1
        apply sum_congr rfl
        intro R hR
        have hr := mem_powerset.mp hR
        have hd : Disjoint A (R ∩ Q) := by
          apply disjoint_left.mpr
          intro p hp hpR
          exact (mem_sdiff.mp (hr (mem_inter.mp hpR).1)).2 hp
        have hc : (((A ∪ R) ∩ Q).card : ℝ) = (A.card : ℝ)+(R ∩ Q).card := by
          rw [union_inter_distrib_right,inter_eq_left.mpr hAQ,card_union_of_disjoint hd,Nat.cast_add]
        rw [hc]
        have hh : (A.card : ℝ)+(R ∩ Q).card ≤ r ↔ ((R ∩ Q).card : ℝ) ≤ r-A.card := by
          constructor <;> intro hh <;> linarith
        simp only [hh,mul_ite,mul_one,mul_zero]
  rw [he]
  have htail := bernoulliSubsetMass_restricted_count_tail (P \ A) Q q (-t) (r-A.card)
    (fun p hp => hq p (mem_sdiff.mp hp).1)
  have hb : (∑ R ∈ (P \ A).powerset,
        if ((R ∩ Q).card : ℝ) ≤ r-A.card then bernoulliSubsetMass (P \ A) q R else 0) ≤
      Real.exp (t*(r-A.card)+(Real.exp (-t)-1)*∑ p ∈ (P \ A) ∩ Q, q p) := by
    refine le_trans ?_ (by simpa only [neg_neg] using htail)
    apply sum_le_sum
    intro R hR
    have hnon := bernoulliSubsetMass_nonneg (mem_powerset.mp hR)
      (fun p hp => hq p (mem_sdiff.mp hp).1)
    split_ifs with hc hs
    · exact le_rfl
    · exact False.elim (hs (mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr ht)))
    · exact hnon
    · exact le_rfl
  exact mul_le_mul_of_nonneg_left hb (prod_nonneg (fun p hp => (hq p (hA hp)).1))

end JointDickman

end OAI
