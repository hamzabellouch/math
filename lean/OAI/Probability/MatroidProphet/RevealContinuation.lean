import OAI.Probability.MatroidProphet.BatchReveal

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

theorem RevealTree.continuation_expectation (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (f : β → Finset α → ℝ) :
    bitsExpectation q V (fun S => f (tree.run S) (S \ tree.queried S)) =
      bitsExpectation q V (fun S => bitsExpectation q (V \ tree.queried S)
        (fun T => f (tree.run S) T)) := by
  induction tree generalizing V with
  | leaf b => simp only [run, queried, sdiff_empty, bitsExpectation_const]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have leftSplit := bitsExpectation_insert q W e heW
      (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S))
    rw [hWV] at leftSplit
    have rightSplit := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
        (fun T => f ((RevealTree.query e no yes).run S) T))
    rw [hWV] at rightSplit
    have hSD (S Q : Finset α) (hS : S ⊆ W) :
        S \ insert e Q = S \ Q ∧ insert e S \ insert e Q = S \ Q := by
      have heS : e ∉ S := fun h => heW (hS h)
      constructor <;> ext x <;> by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
      · subst x; simp [heS]
      · simp [hxe]
    have hnoLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S)) =
        bitsExpectation q W (fun S => f (no.run S) (S \ no.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS, (hSD S _ hS).1]
    have hyesLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run (insert e S))
        (insert e S \ (RevealTree.query e no yes).queried (insert e S))) =
        bitsExpectation q W (fun S => f (yes.run S) (S \ yes.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS, (hSD S _ hS).2]
    have hnoRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
          (fun T => f ((RevealTree.query e no yes).run S) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ no.queried S)
          (fun T => f (no.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    have hyesRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried (insert e S))
          (fun T => f ((RevealTree.query e no yes).run (insert e S)) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ yes.queried S)
          (fun T => f (yes.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    rw [leftSplit, rightSplit, hnoLeft, hyesLeft, hnoRight, hyesRight, ihn W hn, ihy W hy]

end MatroidProphet

end OAI
