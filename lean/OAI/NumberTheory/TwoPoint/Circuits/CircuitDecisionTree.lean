import OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree

namespace OAI

/-! A decision tree making at most `d` queries on any branch has Walsh
degree at most `d`. This is the spectral consequence of circuit switching. -/

namespace TwoPointCorrelations

open scoped Classical

lemma WalshDegreeLE.add {n d : ℕ} {F G : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F d) (hG : WalshDegreeLE G d) :
    WalshDegreeLE (fun x => F x + G x) d := by
  have h := hF.sub (hG.smul (-1))
  convert h using 1
  funext x
  ring

inductive BooleanDecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | query (i : Fin n) (low high : BooleanDecisionTree n)

namespace BooleanDecisionTree

def eval {n : ℕ} : BooleanDecisionTree n → BooleanCube n → Bool
  | .leaf b, _ => b
  | .query i low high, x => if x i then high.eval x else low.eval x

def depth {n : ℕ} : BooleanDecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ low high => max low.depth high.depth + 1

noncomputable def indicator {n : ℕ} (c : BooleanDecisionTree n) (x : BooleanCube n) : ℝ :=
  if c.eval x then 1 else 0

theorem indicator_degree {n : ℕ} (c : BooleanDecisionTree n) :
    WalshDegreeLE c.indicator c.depth := by
  induction c with
  | leaf b =>
    cases b <;> exact WalshDegreeLE.const _ _
  | query i low high hl hh =>
    let d := max low.depth high.depth
    have hlow : WalshDegreeLE low.indicator d := hl.mono (Nat.le_max_left _ _)
    have hhigh : WalshDegreeLE high.indicator d := hh.mono (Nat.le_max_right _ _)
    have hbit := literal_indicator_degree i true
    have hnot := literal_indicator_degree i false
    have h := (hnot.mul hlow).add (hbit.mul hhigh)
    have heq : (fun x => (AC0Circuit.literal i false).indicator x * low.indicator x +
        (AC0Circuit.literal i true).indicator x * high.indicator x) =
        (query i low high).indicator := by
      funext x
      cases hx : x i <;>
        simp [indicator, eval, AC0Circuit.indicator, AC0Circuit.eval, hx]
    rw [heq] at h
    simpa only [depth, d, Nat.add_comm 1] using h

end BooleanDecisionTree

lemma WalshDegreeLE.high_coefficient_zero {n d : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F d) (S : Finset (Fin n)) (hS : d < S.card) :
    walshCoefficient F S = 0 := by
  obtain ⟨a, ha⟩ := hF
  unfold walshCoefficient
  simp_rw [ha, Finset.sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [Nat.not_le.mpr hS]

end TwoPointCorrelations

end OAI
