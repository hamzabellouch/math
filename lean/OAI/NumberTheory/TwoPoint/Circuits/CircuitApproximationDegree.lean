import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateComposition

namespace OAI

/-! Degree bookkeeping for the random polynomial construction. The recursive
degree uses the largest child degree, rather than the number of leaves. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma WalshDegreeLE.mono {n p q : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F p) (hpq : p ≤ q) : WalshDegreeLE F q := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun S => if S.card ≤ p then a S else 0, ?_⟩
  intro x
  rw [ha]
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ p
  · simp [hS, hS.trans hpq]
  · simp [hS]

lemma literal_indicator_degree {n : ℕ} (i : Fin n) (b : Bool) :
    WalshDegreeLE (AC0Circuit.literal i b).indicator 1 := by
  have hw : WalshDegreeLE (walsh {i}) 1 := WalshDegreeLE.of_walsh {i} (by simp)
  have hp := (WalshDegreeLE.const (n := n) (1 / 2) 1).sub (hw.smul (1 / 2))
  have hn := (WalshDegreeLE.const (n := n) 1 1).sub hp
  cases b
  · convert hn using 1
    funext x
    simp only [AC0Circuit.indicator, AC0Circuit.eval, Bool.false_eq_true, ite_false,
      walsh, prod_singleton]
    cases x i <;> norm_num [booleanSign]
  · convert hp using 1
    funext x
    simp only [AC0Circuit.indicator, AC0Circuit.eval, ite_true, walsh, prod_singleton]
    cases x i <;> norm_num [booleanSign]

namespace AC0Circuit

def approximationDegree {n : ℕ} (s : ℕ) : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate (k := k) children =>
    (univ.sup fun i => approximationDegree s (children i)) * s * (Nat.log 2 k + 3)
  | .orGate (k := k) children =>
    (univ.sup fun i => approximationDegree s (children i)) * s * (Nat.log 2 k + 3)

end AC0Circuit

end TwoPointCorrelations

end OAI
