import OAI.NumberTheory.Ostmann.Construction.SelectedFinalInteraction
import OAI.NumberTheory.Ostmann.Construction.SelectedFinalComparison

namespace OAI

/-! # Relative reindexing of actual selected-bulk final pairs -/
namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

private theorem sample_relative {X A : Type*} (e f : Equiv.Perm X) (q : X → A) :
    (fun i => (Equiv.arrowCongr e.symm (Equiv.refl A) q) ((f.trans e.symm) i)) =
      Equiv.arrowCongr f.symm (Equiv.refl A) q := by
  funext i
  change q (e (e.symm (f i))) = q (f i)
  rw [Equiv.apply_symm_apply]

theorem selectedFinalRelativePerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e f : FinalParityReassignments n m)
    (i : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFinalRelativePerm role n m bulk hbulk e f i).val =
      copyScheduleOrigin (n + 1) i.val := by
  have hi := selectedFullFinalPerm_origin role n m bulk hbulk e
    ((selectedFullFinalPerm role n m bulk hbulk e).symm (selectedFullFinalPerm role n m bulk hbulk f i))
  rw [Equiv.apply_symm_apply] at hi
  exact hi.symm.trans (selectedFullFinalPerm_origin role n m bulk hbulk f i)

theorem selected_final_pair_reindex {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e f : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F G : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ q, (scheduledPrimePrior role (n + 1) μ q : ℂ) *
      (F (selectedFullSamplePerm role n m bulk hbulk e q) *
        conj (G (selectedFullSamplePerm role n m bulk hbulk f q)))) =
    ∑ q, (scheduledPrimePrior role (n + 1) μ q : ℂ) *
      (F q * conj (G (fun i => q (selectedFinalRelativePerm role n m bulk hbulk e f i)))) := by
  have h := selectedFullSamplePerm_mean role n m bulk hbulk e μ
    (fun q => F q * conj (G (fun i => q (selectedFinalRelativePerm role n m bulk hbulk e f i))))
  apply Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro q _
  have hq := sample_relative (selectedFullFinalPerm role n m bulk hbulk e)
    (selectedFullFinalPerm role n m bulk hbulk f) q
  exact congrArg (fun t => (scheduledPrimePrior role (n + 1) μ q : ℂ) *
    (F (selectedFullSamplePerm role n m bulk hbulk e q) * conj (G t))) hq.symm

end Ostmann

end OAI
