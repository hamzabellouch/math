import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
import OAI.Combinatorics.Progressions.Polynomial.SingleParameterPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

noncomputable def liftCenter (A : PolynomialSlots Unit d w) (i : Fin d)
    (I : Fin i.val → MvPolynomial Unit ℝ) : MvPolynomial Unit ℝ :=
  aeval (Sum.elim X I) (A.center i)

theorem liftCenter_degree (A : PolynomialSlots Unit d w) (i : Fin d)
    (I : Fin i.val → MvPolynomial Unit ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : Unit => 1) (w (earlierSlot i j))) :
    A.liftCenter i I ∈ weightedSupportLE (fun _ : Unit => 1) (w i) := by
  apply weightedSupportLE_aeval (patchVariableWeight w i) (fun _ : Unit => 1)
  · intro v
    cases v with
    | inl a => exact weightedSupportLE_X _ a
    | inr j => exact hI j
  · exact A.degree i

theorem liftCenter_eval (A : PolynomialSlots Unit d w) (i : Fin d)
    (I : Fin i.val → MvPolynomial Unit ℝ) (t : Unit → ℝ) (b : Fin d → ℤ)
    (hI : ∀ j, aeval t (I j) = (b (earlierSlot i j) : ℝ)) :
    aeval t (A.liftCenter i I) = (A.slots t).center (fun j => (b j : ℝ)) i := by
  simp only [liftCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun f : Unit ⊕ Fin i.val → ℝ => aeval f (A.center i))
  funext v
  cases v with
  | inl a => simp
  | inr j => exact hI j

theorem exists_integer_lifts_of_small_residuals (A : PolynomialSlots Unit d w)
    (g : ℕ → Fin d → ℤ) (z : Fin d → ℝ) {N : ℕ} {ε : ℝ}
    (hsmall : ∀ i, (2 : ℝ) ^ (w i + 1) * ε < 1)
    (happrox : ∀ n < N, ∀ i,
      ‖(A.slots (fun _ => (n : ℝ))).residual (g n) i - z i‖ ≤ ε) :
    ∃ I : Fin d → MvPolynomial Unit ℝ,
      (∀ i, I i ∈ weightedSupportLE (fun _ : Unit => 1) (w i)) ∧
      (∀ i (n : ℕ), ∃ a : ℤ, aeval (fun _ => (n : ℝ)) (I i) = a) ∧
      ∀ n < N, ∀ i, aeval (fun _ => (n : ℝ)) (I i) = (g n i : ℝ) := by
  classical
  have hone : ∀ i : Fin d, ∃ Q : MvPolynomial Unit ℝ,
      Q ∈ weightedSupportLE (fun _ : Unit => 1) (w i) ∧
      (∀ n : ℕ, ∃ a : ℤ, aeval (fun _ => (n : ℝ)) Q = a) ∧
      ∀ n < N, aeval (fun _ => (n : ℝ)) Q = (g n i : ℝ) := by
    intro i
    refine Fin.strong_induction_on (motive := fun i => ∃ Q : MvPolynomial Unit ℝ,
      Q ∈ weightedSupportLE (fun _ : Unit => 1) (w i) ∧
      (∀ n : ℕ, ∃ a : ℤ, aeval (fun _ => (n : ℝ)) Q = a) ∧
      ∀ n < N, aeval (fun _ => (n : ℝ)) Q = (g n i : ℝ)) ?_ i
    intro i ih
    have hprev := fun j : Fin i.val => ih (earlierSlot i j) (show earlierSlot i j < i from j.isLt)
    choose I hI hintI heqI using hprev
    let P := A.liftCenter i I + C (z i)
    have hP : P ∈ weightedSupportLE (fun _ : Unit => 1) (w i) :=
      (weightedSupportLE _ _).add_mem (A.liftCenter_degree i I hI) (weightedSupportLE_C _ _ _)
    have hnear : ∀ n < N, ‖(g n i : ℝ) - aeval (fun _ => (n : ℝ)) P‖ ≤ ε := by
      intro n hn
      have heval := A.liftCenter_eval i I (fun _ => (n : ℝ)) (g n)
        (fun j => heqI j n hn)
      simpa only [P, map_add, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        heval, sub_add_eq_sub_sub, TriangularSlots.residual] using happrox n hn i
    obtain ⟨Q, hQ, hint, heq, _⟩ := exists_singleParameter_integer_lift P
      (fun n => g n i) hP (hsmall i) hnear
    exact ⟨Q, hQ, hint, heq⟩
  choose I hI hint heq using hone
  exact ⟨I, hI, hint, fun n hn i => heq i n hn⟩

end PolynomialSlots
end Erdos3

end

end OAI
