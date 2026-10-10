import OAI.RepresentationTheory.FoulkesHowe.SecondLabels
import OAI.RepresentationTheory.FoulkesHowe.FlattenedForm
import OAI.RepresentationTheory.FoulkesHowe.MonomialCut
import OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial

namespace OAI

noncomputable section

namespace Problem346.SecondTransfer

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- At the zero count vector, every row consists entirely of its independent vector. -/
theorem initial_eval {r b : ℕ} (T : SymmetricMultilinearForm (r+1) b V)
    (v : Block r → V) :
    flattenedSymmetricForm T (fun p => v (label (fun _ : Fin r => 0) p)) =
      T (fun i => symMonomial b V (fun _ => v (some i))) := by
  simp only [flattenedSymmetricForm_apply, label_zero]

/-- At the terminal count vector, the first `r` factors in every moving row
are the common vector. This is precisely the product form in the induction hypothesis. -/
theorem terminal_eval (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (v : Block r → V) :
    flattenedSymmetricForm T (fun p => v (label (fun _ : Fin r => r) p)) =
      T (Fin.cons (symMonomial (r+m) V (fun _ => v (some 0)))
        (fun i => symPowMul r m (symMonomial r V (fun _ => v none))
          (symMonomial m V (fun _ => v (some i.succ))))) := by
  rw [flattenedSymmetricForm_apply]
  apply congrArg T
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [label_zero_row, Fin.cons_zero]
  · simp only [label_succ_row, Fin.cons_succ, apply_ite]
    exact symMonomial_cut r m (v none) (v (some i.succ))

/-- The known common-power vanishing implies the terminal labelled expression vanishes. -/
theorem terminal_eval_zero (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0)
    (v : Block r → V) :
    flattenedSymmetricForm T (fun p => v (label (fun _ : Fin r => r) p)) = 0 := by
  rw [terminal_eval]
  exact h (v none) (v (some 0)) (fun i => symMonomial m V (fun _ => v (some i.succ)))

/-- The terminal labelled polynomial is zero, before any degree-shift cancellation. -/
theorem terminal_polynomial_zero {κ : Type*} [Fintype κ] (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0) :
    multilinearPolynomial (flattenedSymmetricForm T) e (label (fun _ : Fin r => r)) = 0 := by
  apply multilinearPolynomial_eq_zero
  exact terminal_eval_zero r m T h

/-- After cancelling all shifts, the initial polynomial identity evaluates to
vanishing on independent pure powers in every slot. -/
theorem independent_powers_zero_of_initial_polynomial_zero
    {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : Module.Basis κ ℂ V)
    (h : multilinearPolynomial (flattenedSymmetricForm T) e
      (label (fun _ : Fin r => 0)) = 0) (v : Fin (r+1) → V) :
    T (fun i => symMonomial b V (fun _ => v i)) = 0 := by
  have hv := (multilinearPolynomial_eq_zero_iff (flattenedSymmetricForm T) e
    (label (fun _ : Fin r => 0))).mp h (fun o => o.elim 0 v)
  simpa only [flattenedSymmetricForm_apply, label_zero, Option.elim_some] using hv

end Problem346.SecondTransfer

end

end OAI
