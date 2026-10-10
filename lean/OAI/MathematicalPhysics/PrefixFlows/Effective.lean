import Mathlib
import OAI.Computability.Interspersed.Machines
import OAI.MathematicalPhysics.PrefixFlows.Model

namespace OAI

/-! Effective force families and loading pulses. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
abbrev RationalCode := ℤ × ℕ

def RationalCode.value (q : RationalCode) : ℝ := (q.1 : ℝ) / (q.2 + 1 : ℝ)
def accuracy (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop :=
  ∃ a : ℕ → RationalCode, Computable a ∧
    ∀ n, |r - (a n).value| ≤ accuracy n

 
noncomputable def coordinatePartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 4) (f : Spacetime → E) (z : Spacetime) : E :=
  fderivWithin ℝ f future z (Pi.single i 1)

noncomputable def mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List (Fin 4) → (Spacetime → E) → (Spacetime → E)
  | [], f => f
  | i :: α, f => coordinatePartial i (mixed α f)

abbrev RationalPoint := RationalCode × RationalCode × RationalCode × RationalCode

def RationalPoint.value (q : RationalPoint) : Spacetime :=
  ![q.1.value, q.2.1.value, q.2.2.1.value, q.2.2.2.value]

abbrev EvaluationQuery := ℕ × List ℕ × List (Fin 4) × RationalPoint × Fin 3 × ℕ
abbrev BoundQuery := ℕ × List ℕ × List (Fin 4)

 

def EffectiveFamily (F : Machine → List ℕ → Field) : Prop :=
  ∃ evaluate : EvaluationQuery → RationalCode,
  ∃ bound : BoundQuery → ℕ,
    Computable evaluate ∧ Computable bound ∧
    ∀ M, M.WellFormed → ∀ w, M.ValidInput w →
      (∀ α q (i : Fin 3) n, 0 ≤ q.value 0 →
        |mixed α (F M w) q.value i -
          (evaluate (M.code, w, α, q, i, n)).value| ≤ accuracy n) ∧
      (∀ α z, z ∈ future → ∀ i : Fin 3,
        |mixed α (F M w) z i| ≤ (bound (M.code, w, α) : ℝ))

 
def UnitPulse (P : Field) : Prop :=
  ContDiff ℝ ∞ P ∧ ∃ ε : ℝ, 0 < ε ∧ ε < (1 / 2 : ℝ) ∧
    ∀ z, z 0 ≤ ε ∨ 1 - ε ≤ z 0 → P z = 0

 

noncomputable def assemble (template : Machine → Field)
    (loading : Machine → List ℕ → Field) (M : Machine) (w : List ℕ) : Field :=
  fun z => if z 0 < 1 then loading M w z
    else template M (point (Int.fract (z 0)) (position z))

 
def InstanceContract (ν : ℝ) (M : Machine) (w : List ℕ) (f : Field) : Prop :=
  GloballySmooth f ∧ SpacePeriodic f ∧ MeanZero f ∧
  (∀ t, 1 ≤ t → ∀ x, f (point (t + 1) x) = f (point t x)) ∧
  ∃ (u : Field) (p : Pressure) (X : ℝ → Space),
    GloballySmooth u ∧ GloballySmooth p ∧ ClassicalSolution ν f u p ∧
    (∀ v q, ClassicalSolution ν f v q →
      ∀ t, 0 ≤ t → ∀ x, v (point t x) = u (point t x) ∧ q (point t x) = p (point t x)) ∧
    BoundedEnergy u ∧ MaterialTrajectory u X ∧
    (∀ Y, MaterialTrajectory u Y → ∀ t, 0 ≤ t → Y t = X t) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ observed (X t)) ↔ M.Halts w)

 

def InterspersedHistoryConclusion (ν : ℝ) : Prop :=
  ∃ template : Machine → Field,
  ∃ loading : Machine → List ℕ → Field,
    EffectiveFamily (assemble template loading) ∧
    (∀ M, M.WellFormed → UnitPulse (template M)) ∧
    (∀ M, M.WellFormed → ∀ w, M.ValidInput w →
      UnitPulse (loading M w) ∧
      InstanceContract ν M w (assemble template loading M w))
end PrefixFlows
end

end OAI
