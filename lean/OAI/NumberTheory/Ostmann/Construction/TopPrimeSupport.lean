import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedCoprimalityBound

namespace OAI

/-! # Actual-prime collisions and coprimality to a fixed external integer -/

namespace Ostmann

open scoped BigOperators Classical

inductive TopPrimeCondition (V : Type*) where
  | distinct (left right : V)
  | external (coordinate : V) (value : ℤ)

def TopPrimeCondition.coordinate {V : Type*} : TopPrimeCondition V → V
  | .distinct a _ => a
  | .external a _ => a

def TopPrimeCondition.formula {V : Type*} : TopPrimeCondition V → HistoryFormula V
  | .distinct _ b => .prime b
  | .external _ N => .external N

def TopPrimeCondition.target {V : Type*} : TopPrimeCondition V → (V → ℕ) → ℤ
  | .distinct _ b, x => x b
  | .external _ N, _ => N

def TopPrimeCondition.Holds {V : Type*} (g : TopPrimeCondition V) (x : V → ℕ) : Prop :=
  (x g.coordinate).Coprime (g.target x).natAbs

theorem TopPrimeCondition.distinct_holds_iff {V : Type*} (a b : V) (x : V → ℕ)
    (ha : (x a).Prime) (hb : (x b).Prime) :
    (TopPrimeCondition.distinct a b).Holds x ↔ x a ≠ x b := by
  simpa only [Holds, coordinate, target, Int.natAbs_natCast] using Nat.coprime_primes ha hb

theorem TopPrimeCondition.formula_value {V : Type*} (g : TopPrimeCondition V) (x : V → ℕ) :
    g.formula.value (fun i => (x i : ℚ)) = g.target x := by
  cases g <;> simp only [formula, target, HistoryFormula.value_prime,
    HistoryFormula.value_external, Int.cast_natCast]

theorem TopPrimeCondition.formula_cost {V : Type*} (g : TopPrimeCondition V) :
    g.formula.cost = 1 := by cases g <;> rfl

theorem TopPrimeCondition.formula_denominator {V : Type*} (g : TopPrimeCondition V) :
    g.formula.cleared.denominator = 1 := by cases g <;> rfl

def TopPrimeCondition.Bounded {V : Type*} (R : ℝ) : TopPrimeCondition V → Prop
  | .distinct _ _ => True
  | .external _ N => |(N : ℝ)| ≤ R

theorem TopPrimeCondition.formula_inputs {V : Type*} (g : TopPrimeCondition V)
    (R : ℝ) (hg : g.Bounded R) : g.formula.InputsBounded R := by
  cases g <;> exact hg

/-- This bound allows repeated coordinates or a zero external integer. Such
conditions have empty support and are covered by the same proved alternative. -/
theorem top_prime_support_bound {A J : Type*} [Fintype A] [Nonempty A] [Fintype J] {m : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (checks : J → TopPrimeCondition (Fin (m + 1)))
    (μ : Fin (m + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hbound : ∀ j, (checks j).Bounded R)
    (W : (Fin (m + 1) → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then W x else 0)‖ ≤
      δ + B * (Fintype.card J : ℝ) * (α + Real.log R / V * α) := by
  have hv (x : Fin (m + 1) → A) (_ : W x ≠ 0) (j : J) :
      (checks j).formula.value (fun i => (prime (x i) : ℚ)) =
          (checks j).target (fun i => prime (x i)) ∧
        ¬prime (x (checks j).coordinate) ∣ (checks j).formula.cleared.denominator.natAbs := by
    refine ⟨(checks j).formula_value _, ?_⟩
    rw [TopPrimeCondition.formula_denominator, Int.natAbs_one]
    exact (hprime _).not_dvd_one
  have hh := reconstructed_coprimality_bound prime hpInj hprime
    (fun j => (checks j).formula) (fun j => (checks j).coordinate)
    (fun j x => (checks j).target (fun i => prime (x i))) μ hμ hmass α V R
    (fun _ => α) hα (fun _ => hα) hV hR hmax (fun j a => hmax (checks j).coordinate a)
    hlower hupper (fun j => (checks j).formula_inputs R (hbound j)) W B δ hB hδ hW hv hcancel
  have he (x : Fin (m + 1) → A) :
      (if ∀ j, (prime (x (checks j).coordinate)).Coprime
        ((checks j).target (fun i => prime (x i))).natAbs then W x else 0) =
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then W x else 0) := by
    congr 1
  simpa only [he, TopPrimeCondition.formula_cost, Nat.cast_one, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

end Ostmann

end OAI
