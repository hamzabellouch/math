import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
universe u v

namespace Cotype

abbrev Cube (n : ℕ) := Fin n → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {ι : Type u} [Fintype ι] {E : Type v} [AddCommMonoid E] [Module ℝ E]
    (f : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def cubeL2 {n : ℕ} (f : Cube n → E) : ℝ :=
  Real.sqrt (average (fun ε => ‖f ε‖ ^ 2))

def rademacherSum {n : ℕ} (x : Fin n → E) (ε : Cube n) : E :=
  ∑ i, sign (ε i) • x i

def moment {n : ℕ} (f : Cube n → E) (i : Fin n) : E :=
  average (fun ε => sign (ε i) • f ε)

def radProjection {n : ℕ} (f : Cube n → E) : Cube n → E :=
  rademacherSum E (moment E f)

def KConvex : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : Cube n → E),
  cubeL2 E (radProjection E f) ≤ K * cubeL2 E f

def HasCotype (q : ℝ) : Prop := 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧
  ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * cubeL2 E (rademacherSum E x)

def FiniteCotype : Prop := ∃ q : ℝ, HasCotype E q

def ApproximationProperty : Prop := ∀ (M : Set E), IsCompact M →
  ∀ δ : ℝ, 0 < δ → ∃ S : E →L[ℝ] E,
    FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧
    ∀ x ∈ M, ‖S x - x‖ < δ

def MainTarget [CompleteSpace E] [Nontrivial E] : Prop :=
  ApproximationProperty E →
    (KConvex E ↔ FiniteCotype E ∧ FiniteCotype (E →L[ℝ] ℝ))

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem mainTarget_proved [Nontrivial X] : MainTarget X := by
  sorry

end Cotype

end

end OAI
