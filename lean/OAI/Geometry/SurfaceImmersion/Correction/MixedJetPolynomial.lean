import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVariation

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

inductive MixedExpression where
  | coeff (c : LowJet × ℝ → ℝ)
  | atom (tag : Fin 4) (word : List (Fin 2)) (component : Fin 4) (tail : MixedExpression)
  | add (left right : MixedExpression)

namespace MixedExpression

def eval : MixedExpression → (Fin 4 → Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, z => c (lowJet (G 0) z.1, z.2)
  | .atom i w a e, G, z => jet (G i) w a z.1 * e.eval G z
  | .add e f, G, z => e.eval G z + f.eval G z

def loss : MixedExpression → ℕ
  | .coeff _ => 0
  | .atom i w _ e => (if i = 0 then w.length - 2 else w.length) + e.loss
  | .add e f => max e.loss f.loss

def SmoothCoeffs (O : Set LowJet) : MixedExpression → Prop
  | .coeff c => ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)
  | .atom _ _ _ e => e.SmoothCoeffs O
  | .add e f => e.SmoothCoeffs O ∧ f.SmoothCoeffs O

def ofExpression : Expression → MixedExpression
  | .coeff c => .coeff c
  | .atom w a e => .atom 0 w a (ofExpression e)
  | .add e f => .add (ofExpression e) (ofExpression f)

lemma ofExpression_eval (e : Expression) (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (ofExpression e).eval G z = e.eval (G 0) z := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, eval, Expression.eval, ih]
  | add _ _ ihe ihf => simp only [ofExpression, eval, Expression.eval, ihe, ihf]

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

def sumList {ι : Type*} : List ι → (ι → MixedExpression) → MixedExpression
  | [], _ => .coeff (fun _ => 0)
  | i :: l, f => .add (f i) (sumList l f)

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

def coefficientDerivative (c : LowJet × ℝ → ℝ) (i : Fin 7 × Fin 4) : LowJet × ℝ → ℝ :=
  fun z => fderiv ℝ c z (lowBasis (.inr i), 0)

/-- Only the base-map slot is differentiated. The new direction is one of
the three variation slots, so a third variation uses no extra map slots. -/
def differentiate (j : Fin 3) : MixedExpression → MixedExpression
  | .coeff c => sumList Finset.univ.toList (fun i : Fin 7 × Fin 4 =>
      .atom j.succ (lowWord i.1) i.2 (.coeff (coefficientDerivative c i)))
  | .atom i w a e => if i = 0 then
      .add (.atom j.succ w a e) (.atom i w a (differentiate j e))
    else .atom i w a (differentiate j e)
  | .add e f => .add (differentiate j e) (differentiate j f)

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
