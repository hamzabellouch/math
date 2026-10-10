import OAI.MeasureTheory.Falconer.Estimates.FiniteFamilyOverlap
import Mathlib.Data.Finset.Prod

namespace OAI

/-! Simultaneous large intersections for both factors of a family of
rectangles. The reference rectangle is an actual member of the family. -/
namespace Falconer

 theorem common_rectangular_subsets {α : Type*}
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧
      ∀ j ∈ J,
        ρ^4*(X.card : ℝ)/2 ≤ ((A i₀ ∩ A j).card : ℝ) ∧
        ρ^4*(Y.card : ℝ)/2 ≤ ((B i₀ ∩ B j).card : ℝ) := by
  classical
  have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hYpos : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  let R := fun i => (A i) ×ˢ (B i)
  have hRsub (i) (hi : i ∈ I) : R i ⊆ X ×ˢ Y := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hA i hi ha,hB i hi hb⟩
  have hRsize (i) (hi : i ∈ I) : ρ^2*(X.card : ℝ)*(Y.card : ℝ) ≤ ((R i).card : ℝ) := by
    have hh := mul_le_mul (hsizeA i hi) (hsizeB i hi)
      (mul_pos hρ hYpos).le (Nat.cast_nonneg _)
    simpa only [R,Finset.card_product,Nat.cast_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  obtain ⟨i₀,hi₀,J,hJI,hJ,hrect⟩ := finite_family_common_row I (X ×ˢ Y) R
    hI (hX.product hY) (by positivity : 0 < ρ^2*(X.card : ℝ)*(Y.card : ℝ)) hRsub hRsize
  have hn : (ρ^2*(X.card : ℝ)*(Y.card : ℝ))^2/((X.card : ℝ)*(Y.card : ℝ)) =
      ρ^4*(X.card : ℝ)*(Y.card : ℝ) := by
    field_simp
  have hnorm : (ρ^2*(X.card : ℝ)*(Y.card : ℝ))^2/(2*((X.card : ℝ)*(Y.card : ℝ))) =
      ρ^4*(X.card : ℝ)*(Y.card : ℝ)/2 := by
    field_simp
  simp only [Finset.card_product,Nat.cast_mul,hn] at hJ
  refine ⟨i₀,hi₀,J,hJI,?_,?_⟩
  · apply (mul_le_mul_iff_left₀ (mul_pos hXpos hYpos)).1
    convert hJ using 1 <;> ring
  · intro j hj
    have hh := hrect j hj
    simp only [R,Finset.product_inter_product,Finset.card_product,Nat.cast_mul,hnorm] at hh
    have ha : ((A i₀ ∩ A j).card : ℝ) ≤ (X.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans (hA i₀ hi₀)))
    have hb : ((B i₀ ∩ B j).card : ℝ) ≤ (Y.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans (hB i₀ hi₀)))
    constructor
    · have hx := hh.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
      apply (mul_le_mul_iff_left₀ hYpos).1
      convert hx using 1
      ring
    · have hy := hh.trans (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))
      apply (mul_le_mul_iff_left₀ hXpos).1
      convert hy using 1 <;> ring

end Falconer

end OAI
