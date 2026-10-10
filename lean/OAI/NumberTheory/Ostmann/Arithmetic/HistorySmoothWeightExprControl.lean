import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprDeriv

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
variable {ι : Type*}

def logSize : Expr ι → ℕ
  | .atom _ => 1
  | .fixed _ => 0
  | .add a b | .sub a b | .mul a b | .divide a b => a.logSize + b.logSize

def cancellationDepth : Expr ι → ℕ
  | .atom _ | .fixed _ => 0
  | .add a b | .sub a b => max a.cancellationDepth b.cancellationDepth + 1
  | .mul a b | .divide a b => max a.cancellationDepth b.cancellationDepth

def RelativeControl (x : ι → ℝ) (K : ℝ) : Expr ι → Prop
  | .atom i => x i ≠ 0
  | .fixed c => (c : ℝ) ≠ 0
  | .add a b => a.RelativeControl x K ∧ b.RelativeControl x K ∧
      (Expr.add a b).realEval x ≠ 0 ∧
      |a.realEval x / (Expr.add a b).realEval x| ≤ K ∧
      |b.realEval x / (Expr.add a b).realEval x| ≤ K
  | .sub a b => a.RelativeControl x K ∧ b.RelativeControl x K ∧
      (Expr.sub a b).realEval x ≠ 0 ∧
      |a.realEval x / (Expr.sub a b).realEval x| ≤ K ∧
      |b.realEval x / (Expr.sub a b).realEval x| ≤ K
  | .mul a b | .divide a b => a.RelativeControl x K ∧ b.RelativeControl x K

theorem RelativeControl.value_ne_zero (e : Expr ι) (x : ι → ℝ) (K : ℝ)
    (h : e.RelativeControl x K) : e.realEval x ≠ 0 := by
  induction e with
  | atom i => exact h
  | fixed c => exact h
  | add a b ia ib => exact h.2.2.1
  | sub a b ia ib => exact h.2.2.1
  | mul a b ia ib => exact mul_ne_zero (ia h.1) (ib h.2)
  | divide a b ia ib => exact div_ne_zero (ia h.1) (ib h.2)

theorem RelativeControl.regular (e : Expr ι) (x : ι → ℝ) (K : ℝ)
    (h : e.RelativeControl x K) : e.RealRegularAt x := by
  induction e with
  | atom i => trivial
  | fixed c => trivial
  | add a b ia ib => exact ⟨ia h.1, ib h.2.1⟩
  | sub a b ia ib => exact ⟨ia h.1, ib h.2.1⟩
  | mul a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | divide a b ia ib => exact ⟨ia h.1, ib h.2, RelativeControl.value_ne_zero b x K h.2⟩

def logBudget (e : Expr ι) (K : ℝ) : ℝ := (e.logSize : ℝ) * K ^ e.cancellationDepth

theorem logBudget_nonneg (e : Expr ι) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ e.logBudget K :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hK _)

theorem logBudget_add_le_max (a b : Expr ι) {K : ℝ} (hK : 1 ≤ K) :
    a.logBudget K + b.logBudget K ≤
      ((a.logSize + b.logSize : ℕ) : ℝ) * K ^ max a.cancellationDepth b.cancellationDepth := by
  have ha := pow_le_pow_right₀ hK (Nat.le_max_left a.cancellationDepth b.cancellationDepth)
  have hb := pow_le_pow_right₀ hK (Nat.le_max_right a.cancellationDepth b.cancellationDepth)
  have h := add_le_add
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg a.logSize))
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg b.logSize))
  simpa only [logBudget, Nat.cast_add, add_mul] using h

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
