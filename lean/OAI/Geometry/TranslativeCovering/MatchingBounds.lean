import OAI.Geometry.TranslativeCovering.PoissonDiagrams

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingBounds
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

noncomputable def emptyMatching : Matching I J := ⟨∅, by simp [IsMatching]⟩

lemma all_matchings_eq (w : I × J → ℝ) :
    (∑ M : Matching I J, ∏ e ∈ M.val, w e) =
    1 + ∑ M : Matching I J, if M.val.Nonempty then ∏ e ∈ M.val, w e else 0 := by
  have ht (M : Matching I J) : (∏ e ∈ M.val, w e) =
      (if M.val.Nonempty then ∏ e ∈ M.val, w e else 0) +
      (if M = emptyMatching then 1 else 0) := by
    by_cases he : M.val = ∅
    · have hM : M = emptyMatching := Subtype.ext he
      simp [hM, emptyMatching]
    · have hne := Finset.nonempty_iff_ne_empty.mpr he
      have hM : M ≠ emptyMatching := fun h => he (congrArg Subtype.val h)
      simp only [ite_eq_left hne, ite_eq_right hM, add_zero]
  conv_lhs => arg 2; ext M; rw [ht M]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma all_matchings_le_product (w : I × J → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ M : Matching I J, ∏ e ∈ M.val, w e) ≤ ∏ e, (1+w e) := by
  rw [Finset.prod_one_add]
  let s := Finset.univ.image (Subtype.val : Matching I J → Finset (I × J))
  have hs : (∑ M : Matching I J, ∏ e ∈ M.val, w e) = ∑ M ∈ s, ∏ e ∈ M, w e := by
    dsimp only [s]
    rw [Finset.sum_image]
    intro M _ N _ h
    exact Subtype.ext h
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun M _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
    (fun M _ _ => Finset.prod_nonneg (fun e _ => hw e))

lemma cross_matching_bound (w : I × J → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ M : Matching I J, if M.val.Nonempty then ∏ e ∈ M.val, w e else 0) ≤
      Real.exp (∑ e, w e) - 1 := by
  have h := all_matchings_le_product w hw
  rw [all_matchings_eq] at h
  have hp : (∏ e, (1+w e)) ≤ Real.exp (∑ e, w e) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · exact fun e _ => by linarith [hw e]
    · intro e _
      simpa only [add_comm] using Real.add_one_le_exp (w e)
  linarith

end MatchingBounds

end OAI
