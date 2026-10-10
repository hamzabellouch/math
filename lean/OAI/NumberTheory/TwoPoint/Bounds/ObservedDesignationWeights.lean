import OAI.NumberTheory.TwoPoint.Bounds.CenteredWordMajorant

namespace OAI

/-! Exact designation weights when the ambient prime pool contains unused primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma filtered_power_product (S : Finset ι) (θ : ι → ℝ) (e : ι → ℕ) :
    (∏ i ∈ S, θ i ^ e i) = ∏ i, θ i ^ (if i ∈ S then e i else 0) := by
  calc
    _ = ∏ i, if i ∈ S then θ i ^ e i else 1 := by
      rw [← prod_filter]
      simp
    _ = _ := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> simp

/-- Each observed prime contributes one baseline reciprocal, including
singletons. Only repeated labels contribute additional exponents. -/
theorem observed_designation_reciprocal_factor (label : τ → ι) (lit : τ → Bool)
    (p : ι → ℝ) :
    (∏ t ∈ nonsingletonUnlitSlots label lit, (p (label t))⁻¹) *
      (∏ i ∈ (nonsingletonLitSlots label lit).image label, (p i)⁻¹) *
      (∏ i ∈ singletonLabels label, (p i)⁻¹) =
        (∏ i ∈ univ.image label, (p i)⁻¹) *
          ∏ i ∈ nonsingletonLabels label, (p i)⁻¹ ^
            extraReciprocalExponent (litOccurrences label lit i).card
              (unlitOccurrences label lit i).card := by
  rw [designated_weight_exponents (nonsingletonLitSlots label lit)
    (nonsingletonUnlitSlots label lit) label (fun i => (p i)⁻¹)]
  have hs : (∏ i ∈ singletonLabels label, (p i)⁻¹) =
      ∏ i, (p i)⁻¹ ^ (if i ∈ singletonLabels label then 1 else 0) := by
    simpa only [pow_one] using
      filtered_power_product (singletonLabels label) (fun i => (p i)⁻¹) (fun _ => 1)
  rw [hs, label_image_product univ label (fun i => (p i)⁻¹),
    filtered_power_product (nonsingletonLabels label) (fun i => (p i)⁻¹)
      (fun i => extraReciprocalExponent (litOccurrences label lit i).card
        (unlitOccurrences label lit i).card), ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← pow_add, ← pow_add]
  congr 1
  rw [nonsingleton_lit_fiber, nonsingleton_unlit_fiber]
  by_cases hn : i ∈ nonsingletonLabels label
  · have hc := (mem_filter.mp hn).2
    have hm := lit_unlit_count label lit i
    have hp := litReciprocalExponent_pos (litOccurrences label lit i).card
      (unlitOccurrences label lit i).card (by omega)
    have hns : i ∉ singletonLabels label := by
      simp only [singletonLabels, mem_filter, mem_univ, true_and]
      omega
    simp only [ite_eq_left hn, ite_eq_right hns, add_zero,
      extraReciprocalExponent]
    have hz : (univ.filter (fun t => label t = i)).card ≠ 0 := by
      change (labelOccurrences label i).card ≠ 0
      omega
    simp only [ite_eq_right hz]
    omega
  · have hc : (labelOccurrences label i).card < 2 := by
      simpa only [nonsingletonLabels, mem_filter, mem_univ, true_and, not_le] using hn
    simp only [ite_eq_right hn, card_empty, litReciprocalExponent, ↓reduceIte,
      add_zero, zero_add]
    by_cases hzero : (labelOccurrences label i).card = 0
    · have hns : i ∉ singletonLabels label := by
        simp [singletonLabels, hzero]
      simp only [ite_eq_right hns]
      change 0 = if (labelOccurrences label i).card = 0 then 0 else 1
      rw [ite_eq_left hzero]
    · have hone : (labelOccurrences label i).card = 1 := by omega
      have hss : i ∈ singletonLabels label := by simp [singletonLabels, hone]
      simp only [ite_eq_left hss]
      change 1 = if (labelOccurrences label i).card = 0 then 0 else 1
      rw [ite_eq_right hzero]

theorem observed_designation_reciprocal_bound (label : τ → ι) (lit : τ → Bool)
    (p : ι → ℝ) (H : ℝ) (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ t ∈ nonsingletonUnlitSlots label lit, (p (label t))⁻¹) *
      (∏ i ∈ (nonsingletonLitSlots label lit).image label, (p i)⁻¹) *
      (∏ i ∈ singletonLabels label, (p i)⁻¹) ≤
        (∏ i ∈ univ.image label, (p i)⁻¹) * H⁻¹ ^
          (∑ i ∈ nonsingletonLabels label,
            extraReciprocalExponent (litOccurrences label lit i).card
              (unlitOccurrences label lit i).card) := by
  rw [observed_designation_reciprocal_factor, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left
  · apply prod_le_prod₀
    · intro i _
      exact pow_nonneg (inv_nonneg.mpr (hH.trans_le (hp i)).le) _
    · intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hH.trans_le (hp i)).le)
        (inv_anti₀ hH (hp i)) _
  · exact prod_nonneg (fun i _ => inv_nonneg.mpr (hH.trans_le (hp i)).le)

noncomputable def designationLit (U : Finset τ) (t : τ) : Bool := decide (t ∉ U)

lemma designationLit_unlit (label : τ → ι) (U : Finset τ)
    (hU : U ⊆ nonsingletonSlots label) :
    nonsingletonUnlitSlots label (designationLit U) = U := by
  ext t
  simp only [nonsingletonUnlitSlots, mem_filter, mem_univ, true_and, designationLit,
    decide_eq_false_iff_not, not_not]
  constructor
  · exact And.right
  · intro ht
    exact ⟨(mem_filter.mp (hU ht)).2, ht⟩

lemma designationLit_lit (label : τ → ι) (U : Finset τ) :
    nonsingletonLitSlots label (designationLit U) = nonsingletonSlots label \ U := by
  ext t
  simp [nonsingletonLitSlots, nonsingletonSlots, designationLit, and_comm]

/-- The coefficient in the full signed expansion retains the actual
extra-exponent saving even when unused primes occur in the ambient pool. -/
theorem full_word_designated_reciprocal_bound (label : τ → ι) (U : Finset τ)
    (hU : U ⊆ nonsingletonSlots label) (p : ι → ℕ) (H : ℝ)
    (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^
        (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) := by
  simpa only [designationLit_unlit label U hU, designationLit_lit, designatedReciprocal]
    using observed_designation_reciprocal_bound label (designationLit U)
      (fun i => (p i : ℝ)) H hH hp

end TwoPointCorrelations

end OAI
