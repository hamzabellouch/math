import Mathlib
import OAI.Geometry.HyperbolicGroups.Template
import OAI.Geometry.HyperbolicGroups.Budget

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction

namespace IncidenceTemplate

abbrev Row := Fin 7 ⊕ (Unit ⊕ TwoPath)

instance instRowDecidableEq : DecidableEq Row := instDecidableEqSum

lemma card_rows : Fintype.card Row = 98 := by
  simp [Fintype.card_sum, card_twoPaths]

/-- The 98 distinct array types of the exact master pattern. -/
def rowSupport : Row → Finset Field
  | Sum.inl i => (fan i).map Function.Embedding.inl
  | Sum.inr (Sum.inl _) => Finset.univ.map Function.Embedding.inl
  | Sum.inr (Sum.inr τ) => squareSupport τ

def rowCost : Row → ℤ
  | Sum.inl i => (fan i).card - 2
  | Sum.inr (Sum.inl _) => 12
  | Sum.inr (Sum.inr _) => 2

def pattern : SparsePattern.Pattern Field Row where
  support := rowSupport
  cost := rowCost
  nonneg r := by
    rcases r with i | (_ | τ)
    · have h := fan_card_lower i
      dsimp [rowCost]
      omega
    · norm_num [rowCost]
    · norm_num [rowCost]

lemma pattern_exponent (W : Finset Field) :
    pattern.exponent W = criticalExponent W := by
  classical
  change (W.card : ℤ) - (∑ r, if rowSupport r ⊆ W then rowCost r else 0) = _
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  dsimp only [rowSupport, rowCost]
  simp only [Finset.map_inl_subset_iff_subset_toLeft, Finset.univ_subset_iff]
  rw [count_split, Nat.cast_add, Nat.cast_sum]
  unfold criticalExponent coreExponent freshScore
  rw [Finset.sum_sub_distrib]
  ring_nf
  rfl

lemma rowSupport_card (r : Row) : 3 ≤ (rowSupport r).card := by
  rcases r with i | (_ | τ)
  · simpa [rowSupport] using fan_card_lower i
  · simp [rowSupport, card_edges]
  · have hn := twoPath_ne τ
    simp [rowSupport, squareSupport, hn]

lemma admissible_card (S : Finset Field) (hS : Admissible S) : S.card ≤ 3 := by
  rcases hS with ⟨he, hc⟩ | ⟨τ, _, hc⟩
  · have hh := Finset.card_toLeft_add_card_toRight (u := S)
    rw [he, Finset.card_empty, add_zero] at hh
    exact hh ▸ hc.1
  · omega

lemma admissible_subset {S T : Finset Field} (hT : Admissible T)
    (hST : S ⊆ T) : Admissible S := by
  rcases hT with ⟨ht, hc, hf⟩ | ⟨τ, hs, hc⟩
  · left
    refine ⟨?_, (Finset.card_le_card (Finset.toLeft_subset_toLeft hST)).trans hc, ?_⟩
    · exact Finset.subset_empty.mp (ht ▸ Finset.toRight_subset_toRight hST)
    · intro i
      exact (Finset.card_le_card (Finset.inter_subset_inter_right
        (Finset.toLeft_subset_toLeft hST))).trans (hf i)
  · exact Or.inr ⟨τ, hST.trans hs, (Finset.card_le_card hST).trans hc⟩

/-- The closure and its whole-integer positive margin with no uninstantiated
budget hypotheses: this is the exact master-pattern closure of Section 4. -/
theorem exists_critical_closure (I : Finset Field) (e : Field) (he : e ∉ I)
    (hadm : Admissible (insert e I)) :
    ∃ U : Finset Field, I ⊆ U ∧ criticalExponent U = I.card ∧ e ∉ U ∧
      ∀ V : Finset Field, V.Nonempty → Disjoint V U →
        1 ≤ criticalExponent (U ∪ V) - criticalExponent U := by
  have hcard := admissible_card _ hadm
  rw [Finset.card_insert_of_notMem he] at hcard
  have hsmall : I.card ≤ 2 := by omega
  have hnone (r : Row) : ¬rowSupport r ⊆ I := by
    intro hs
    have hle := Finset.card_le_card hs
    have hlo := rowSupport_card r
    omega
  have hi : pattern.exponent I = I.card :=
    pattern.exponent_eq_card I hnone
  have hIadm := admissible_subset hadm (Finset.subset_insert e I)
  obtain ⟨U, hu, hc, heu, hgap⟩ := pattern.critical_closure I e he hi
    (fun W hW => by rw [pattern_exponent]; exact criticalExponent_admissible I W hIadm hW)
    (fun W hW => by rw [pattern_exponent]; exact criticalExponent_admissible _ W hadm hW)
  refine ⟨U, hu, ?_, heu, ?_⟩
  · simpa only [pattern_exponent] using hc
  · intro V hV hdis
    simpa only [pattern_exponent] using hgap V hV hdis

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
