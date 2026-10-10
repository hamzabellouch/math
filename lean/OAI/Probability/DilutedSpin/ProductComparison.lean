import OAI.Probability.DilutedSpin.InsertionPoint

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Replacing each independent coordinate with a law that decreases every
conditional expectation decreases the full product expectation. -/
lemma expect_pi_comparison {α : Type} [Fintype α] [Nonempty α] (k : ℕ)
    (P Q : Fin k → FiniteLaw α) (F : (Fin k → α) → ℝ)
    (h : ∀ (i : Fin k) (x : Fin k → α),
      (P i).expect (fun a => F (Function.update x i a)) ≤
        (Q i).expect (fun a => F (Function.update x i a))) :
    (pi P).expect F ≤ (pi Q).expect F := by
  classical
  induction k with
  | zero =>
      have hh : P=Q := by funext i; exact Fin.elim0 i
      rw [hh]
  | succ k ih =>
      rw [expect_pi_cons,expect_pi_cons]
      calc
        _ ≤ (P 0).expect (fun a =>
          (pi (fun i : Fin k => Q i.succ)).expect (fun x => F (Fin.cons a x))) := by
          apply expect_mono
          intro a
          apply ih
          intro i x
          have hh := h i.succ (Fin.cons a x)
          have he (b : α) : Fin.cons a (Function.update x i b)=
              Function.update (Fin.cons a x : Fin (k+1) → α) i.succ b := by
            funext j
            refine Fin.cases ?_ (fun j => ?_) j
            · simp [Function.update,(Fin.succ_ne_zero i).symm]
            · by_cases hji : j=i
              · subst j; simp [Function.update]
              · simp [Function.update,hji,Fin.succ_inj]
          simpa only [he] using hh
        _ = (pi (fun i : Fin k => Q i.succ)).expect
            (fun x => (P 0).expect (fun a => F (Fin.cons a x))) := expect_comm _ _ _
        _ ≤ (pi (fun i : Fin k => Q i.succ)).expect
            (fun x => (Q 0).expect (fun a => F (Fin.cons a x))) := by
          apply expect_mono
          intro x
          let a : α := Classical.choice (inferInstance : Nonempty α)
          have hh := h 0 (Fin.cons a x)
          simpa only [Fin.update_cons_zero] using hh
        _ = _ := expect_comm _ _ _

end DilutedSpinGlass.FiniteLaw

end

end OAI
