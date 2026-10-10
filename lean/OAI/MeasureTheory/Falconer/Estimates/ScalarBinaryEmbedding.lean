import OAI.MeasureTheory.Falconer.Recursion.ScalarBinaryBranch
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! Constructing the binary point map from nested finite forks. The
 resulting map has exactly the bit-update bounds used in the sumset step. -/
namespace Falconer

 theorem scalar_binary_embedding (N : ℕ) (P : ℕ → Finset ℝ → Prop)
    (lo hi : ℕ → ℝ) (S : Finset ℝ) (hS : P 0 S)
    (hne : ∀ n ≤ N, ∀ E, P n E → E.Nonempty)
    (hstep : ∀ n < N, ∀ E, P n E → ∃ E0 E1 : Finset ℝ,
      E0 ⊆ E ∧ E1 ⊆ E ∧ P (n+1) E0 ∧ P (n+1) E1 ∧
      ∀ x ∈ E0, ∀ y ∈ E1, lo n ≤ |x-y| ∧ |x-y| ≤ hi n) :
    ∃ f : (Fin N → Bool) → ℝ, (∀ w, f w ∈ S) ∧
      ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
        lo n ≤ |f (Function.update w n true)-f w| ∧
        |f (Function.update w n true)-f w| ≤ hi n := by
  classical
  induction N generalizing P lo hi S with
  | zero =>
    obtain ⟨x,hx⟩ := hne 0 le_rfl S hS
    exact ⟨fun _ => x,fun _ => hx,fun n => Fin.elim0 n⟩
  | succ N ih =>
    obtain ⟨S0,S1,h0S,h1S,hP0,hP1,hcross⟩ := hstep 0 (by omega) S hS
    let P' := fun n E => P (n+1) E
    have hn' : ∀ n ≤ N, ∀ E, P' n E → E.Nonempty := by
      intro n hn E hE
      exact hne (n+1) (by omega) E hE
    have hs' : ∀ n < N, ∀ E, P' n E → ∃ E0 E1 : Finset ℝ,
        E0 ⊆ E ∧ E1 ⊆ E ∧ P' (n+1) E0 ∧ P' (n+1) E1 ∧
        ∀ x ∈ E0, ∀ y ∈ E1, lo (n+1) ≤ |x-y| ∧ |x-y| ≤ hi (n+1) := by
      intro n hn E hE
      exact hstep (n+1) (by omega) E hE
    obtain ⟨f0,hf0,hb0⟩ := ih P' (fun n => lo (n+1)) (fun n => hi (n+1)) S0 hP0 hn' hs'
    obtain ⟨f1,hf1,hb1⟩ := ih P' (fun n => lo (n+1)) (fun n => hi (n+1)) S1 hP1 hn' hs'
    let f : (Fin (N+1) → Bool) → ℝ := fun w => if w 0 = true then f1 (Fin.tail w) else f0 (Fin.tail w)
    refine ⟨f,?_,?_⟩
    · intro w
      dsimp only [f]
      split_ifs
      · exact h1S (hf1 _)
      · exact h0S (hf0 _)
    · intro n
      refine Fin.cases ?_ (fun j => ?_) n
      · intro w hw
        have hw0 : w 0 = false := hw 0 (by simp)
        dsimp only [f]
        simp only [Function.update_self,ite_true,hw0,Bool.false_eq_true,ite_false,Fin.tail_update_zero]
        have hh := hcross (f0 (Fin.tail w)) (hf0 _) (f1 (Fin.tail w)) (hf1 _)
        simpa only [Fin.val_zero,abs_sub_comm] using hh
      · intro w hw
        have hwt : ScalarBinaryTail j (Fin.tail w) := by
          intro q hq
          exact hw q.succ (by simpa only [Fin.val_succ] using Nat.succ_le_succ hq)
        have hzero : (0 : Fin (N+1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        dsimp only [f]
        rw [Function.update_of_ne hzero,Fin.tail_update_succ]
        by_cases hw0 : w 0 = true
        · simp only [hw0,ite_true]
          exact hb1 j (Fin.tail w) hwt
        · simp only [ite_eq_right hw0]
          exact hb0 j (Fin.tail w) hwt

end Falconer

end OAI
