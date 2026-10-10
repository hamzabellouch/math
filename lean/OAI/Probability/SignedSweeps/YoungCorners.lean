import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def IsRowCorner (lam : YoungDiagram) (i : ℕ) : Prop :=
  lam.rowLen (i + 1) < lam.rowLen i

lemma rowCorner_mem (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    (i, lam.rowLen i - 1) ∈ lam := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  unfold IsRowCorner at hi
  omega

lemma rowCorner_max (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i)
    {c : ℕ × ℕ} (hc : c ∈ lam) (hic : (i, lam.rowLen i - 1) ≤ c) :
    c = (i, lam.rowLen i - 1) := by
  have hi0 := hic.1
  have hi1 := hic.2
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hrow : c.1 = i := by
    by_contra hne
    have hlt : i + 1 ≤ c.1 := by omega
    have hh := lam.rowLen_anti (i + 1) c.1 hlt
    unfold IsRowCorner at hi
    omega
  have hcol : c.2 = lam.rowLen i - 1 := by
    rw [hrow] at hm
    omega
  exact Prod.ext hrow hcol

def eraseRowCorner (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) : YoungDiagram where
  cells := lam.cells.erase (i, lam.rowLen i - 1)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    have ha := lam.isLowerSet hab hb
    apply Finset.mem_erase.mpr
    refine ⟨?_, ha⟩
    intro he
    subst b
    exact hne (rowCorner_max lam hi hb hab)

lemma eraseRowCorner_le (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    eraseRowCorner lam hi ≤ lam := by
  intro c hc
  exact (Finset.mem_erase.mp hc).2

lemma eraseRowCorner_card (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    (eraseRowCorner lam hi).card = lam.card - 1 := by
  change (lam.cells.erase (i, lam.rowLen i - 1)).card = lam.cells.card - 1
  exact Finset.card_erase_of_mem (rowCorner_mem lam hi)

lemma eraseRowCorner_rowLen (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i)
    (k : ℕ) :
    (eraseRowCorner lam hi).rowLen k = if k = i then lam.rowLen k - 1 else lam.rowLen k := by
  rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row, eraseRowCorner, Finset.filter_erase]
  change ((lam.row k).erase (i, lam.rowLen i - 1)).card = _
  by_cases hk : k = i
  · subst k
    rw [ite_eq_left rfl, Finset.card_erase_of_mem]
    · exact congrArg (· - 1) (lam.rowLen_eq_card.symm)
    · exact YoungDiagram.mk_mem_row_iff.mpr (rowCorner_mem lam hi)
  · rw [ite_eq_right hk, Finset.erase_eq_of_notMem]
    · exact lam.rowLen_eq_card.symm
    · simp only [YoungDiagram.mem_row_iff, not_and]
      intro _ hc
      exact hk hc.symm

def predecessorPartition {n : ℕ} (lam : Partition (n + 1)) {i : ℕ}
    (hi : IsRowCorner lam.1 i) : Partition n :=
  ⟨eraseRowCorner lam.1 hi, by rw [eraseRowCorner_card, lam.2, Nat.add_sub_cancel]⟩

lemma predecessorPartition_injective {n : ℕ} (lam : Partition (n + 1)) :
    Function.Injective (fun i : {i : ℕ // IsRowCorner lam.1 i} =>
      predecessorPartition lam i.2) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  have hrow := congrArg (fun μ : Partition n => μ.1.rowLen i.1) he
  change (eraseRowCorner lam.1 i.2).rowLen i.1 =
    (eraseRowCorner lam.1 j.2).rowLen i.1 at hrow
  rw [eraseRowCorner_rowLen, eraseRowCorner_rowLen, ite_eq_left rfl, ite_eq_right hij] at hrow
  have hp := i.2
  unfold IsRowCorner at hp
  omega

end SignedSweeps
end

end OAI
