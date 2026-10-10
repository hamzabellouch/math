import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ENNReal

lemma profile_child_cardND {V α : Type*} [MeasurableSpace V]
    (μ : Measure V) [IsFiniteMeasure μ] (A : Finset α) (cell : α → Set V) (parent : Set V)
    (hdisj : (A : Set α).PairwiseDisjoint cell)
    (hm : ∀ i ∈ A, MeasurableSet (cell i)) (hsub : ∀ i ∈ A, cell i ⊆ parent)
    {R ma mp err : ℝ} (hR : 0 < R)
    (hlower : ∀ i ∈ A, R^(-mp-err) ≤ (μ (cell i)).toReal)
    (hupper : (μ parent).toReal ≤ R^(-ma+err)) :
    (A.card:ℝ) ≤ R^(mp-ma+2*err) := by
  have hsum : (A.card:ℝ)*R^(-mp-err) ≤ (μ parent).toReal := by
    calc
      _ = ∑ _i ∈ A, R^(-mp-err) := by simp
      _ ≤ ∑ i ∈ A, (μ (cell i)).toReal := Finset.sum_le_sum hlower
      _ = (μ (⋃ i ∈ A, cell i)).toReal := by
        rw [measure_biUnion_finset hdisj hm,ENNReal.toReal_sum]
        intro i _; exact measure_ne_top _ _
      _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (iUnion₂_subset hsub))
  have hmul : (A.card:ℝ)*R^(-mp-err) ≤ R^(-ma+err) := hsum.trans hupper
  have he : R^(mp-ma+2*err)*R^(-mp-err)=R^(-ma+err) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  rw [← he] at hmul
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR _)).mp hmul

lemma profile_pair_cardND {V α β : Type*} [MeasurableSpace V]
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Finset α) (B : Finset β) (cell₁ : α → Set V) (cell₂ : β → Set V) (X Y : Set V)
    (hd₁ : (A : Set α).PairwiseDisjoint cell₁) (hd₂ : (B : Set β).PairwiseDisjoint cell₂)
    (hm₁ : ∀ i ∈ A, MeasurableSet (cell₁ i)) (hm₂ : ∀ j ∈ B, MeasurableSet (cell₂ j))
    (hs₁ : ∀ i ∈ A, cell₁ i ⊆ X) (hs₂ : ∀ j ∈ B, cell₂ j ⊆ Y)
    {R ma₁ ma₂ mp₁ mp₂ err₁ err₂ : ℝ} (hR : 0<R)
    (hl₁ : ∀ i ∈ A, R^(-mp₁-err₁) ≤ (μ (cell₁ i)).toReal)
    (hl₂ : ∀ j ∈ B, R^(-mp₂-err₂) ≤ (ν (cell₂ j)).toReal)
    (hu₁ : (μ X).toReal ≤ R^(-ma₁+err₁)) (hu₂ : (ν Y).toReal ≤ R^(-ma₂+err₂)) :
    (A.card:ℝ)*B.card ≤ R^((mp₁-ma₁)+(mp₂-ma₂)+2*(err₁+err₂)) := by
  calc
    _ ≤ R^(mp₁-ma₁+2*err₁)*R^(mp₂-ma₂+2*err₂) :=
      mul_le_mul (profile_child_cardND μ A cell₁ X hd₁ hm₁ hs₁ hR hl₁ hu₁)
        (profile_child_cardND ν B cell₂ Y hd₂ hm₂ hs₂ hR hl₂ hu₂)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
