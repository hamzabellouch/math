import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungResolution

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I] {n : I → ℕ} {N : ℕ}

def orderedBlocks (n : I → ℕ) : (Σₗ i, Fin (n i)) ≃o Fin (∑i,n i) :=
  (Fintype.orderIsoFinOfCardEq (Σₗ i, Fin (n i)) (by simp)).symm

def blockPerm (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : ∀i, Equiv.Perm (Fin (n i))) :
    Equiv.Perm (Fin N) := (toLex.trans e.toEquiv).permCongr (Equiv.Perm.sigmaCongrRight g)

omit [Fintype I] in
@[simp] lemma blockPerm_apply (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (i : I) (a : Fin (n i)) :
    blockPerm e g (e (toLex ⟨i,a⟩)) = e (toLex ⟨i,g i a⟩) := by
  simp [blockPerm, Equiv.permCongr_apply]

omit [Fintype I] in
private lemma block_lt_iff (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (i j : I) (a : Fin (n i)) (b : Fin (n j)) :
    e (toLex ⟨i,a⟩) < e (toLex ⟨j,b⟩) ↔ i < j ∨ ∃ h : i = j, h ▸ a < b :=
  e.lt_iff_lt.trans Sigma.lex_iff

omit [Fintype I] in
private lemma block_le_iff (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (i j : I) (a : Fin (n i)) (b : Fin (n j)) :
    e (toLex ⟨i,a⟩) ≤ e (toLex ⟨j,b⟩) ↔ i < j ∨ ∃ h : i = j, h ▸ a ≤ b :=
  e.le_iff_le.trans Sigma.lex_iff

omit [Fintype I] in
lemma pairWeight_sameBlock (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) (i : I) (a b : Fin (n i)) :
    pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex ⟨i,b⟩)) =
      pairWeight (fun a => β (e (toLex ⟨i,a⟩))) (g i) a b := by
  simp only [pairWeight, blockPerm_apply, block_lt_iff, block_le_iff]
  simp

omit [Fintype I] in
lemma pairWeight_differentBlock (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool)
    {i j : I} (hji : j≠i) (a : Fin (n i)) (b : Fin (n j)) :
    pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex ⟨j,b⟩)) = 1 := by
  simp only [pairWeight, blockPerm_apply, block_lt_iff, block_le_iff]
  rcases lt_or_gt_of_ne hji with h | h
  · simp [h, hji, hji.symm, not_lt_of_gt h]
  · simp [hji, not_lt_of_gt h]

theorem koszulSign_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) :
    koszulSign β (blockPerm e g) = ∏i, koszulSign (fun a => β (e (toLex ⟨i,a⟩))) (g i) := by
  rw [koszulSign_eq_prod,← Equiv.prod_comp e.toEquiv]
  change (∏x : Σ i, Fin (n i), ∏b, pairWeight β (blockPerm e g) (e (toLex x)) b)=_
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [koszulSign_eq_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [← Equiv.prod_comp e.toEquiv]
  change (∏y : Σ j, Fin (n j), pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex y)))=_
  rw [Fintype.prod_sigma]
  rw [Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro b _
    exact pairWeight_sameBlock e g β i a b
  · intro j _ hji
    apply Finset.prod_eq_one
    intro b _
    exact pairWeight_differentBlock e g β hji a b
  · simp

end BinaryCoordinateSweeps.Signed

end

end OAI
