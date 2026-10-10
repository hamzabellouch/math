import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier
import OAI.NumberTheory.Ostmann.Construction.SelectedBulkPermutation

namespace OAI

/-! # The compensation mask is invariant under every bulk reassignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkPerm_active {B J : Type*} (slot : J ↪ B)
    (active : B → Bool) (hactive : ∀ j, active (slot j) = true)
    (e : Equiv.Perm J) (i : B) : active (selectedBulkPerm slot e i) = active i := by
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j with
  | inl j => simp only [selectedIndexEquiv_inl, selectedBulkPerm_bulk, hactive]
  | inr j =>
    change active (selectedBulkPerm slot e j.val) = active j.val
    rw [selectedBulkPerm_nonbulk slot e j.val j.property]

theorem movingTemplateExternalMultiplier_bulk_action
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (outside : List ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (x : MovingRegularSlot n r m → P) (z y : ℝ) :
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
      (selectedBulkSample (movingTemplateBulk n r m) e x) z y =
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal x z y := by
  let E := (selectedBulkPerm (movingTemplateBulk n r m) e).symm
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  let _ : ∀ i, Fact (q (E i)).Prime := fun i => ⟨hP _ (x (E i)).property⟩
  have ha : (fun i => active (E i)) = active := by
    funext i
    exact selectedBulkPerm_active (movingTemplateBulk n r m) active hactive e.symm i
  have h := naturalRegularMultiplier_equiv E q (fun i => hP _ (x i).property) active greg
    outside.prod ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s
  dsimp only at h
  rw [ha] at h
  unfold movingTemplateExternalMultiplier
  dsimp only
  exact congrArg (fun a : ℝ =>
    (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) * a) h

end Ostmann

end OAI
