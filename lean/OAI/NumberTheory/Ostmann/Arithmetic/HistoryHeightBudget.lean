import OAI.NumberTheory.Ostmann.Characters.RationalHistoryDegree
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryHeight

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
variable {ι : Type*}

def fixedLiterals : Expr ι → List ℤ
  | .atom _ => []
  | .fixed c => [c]
  | .add a b | .sub a b | .mul a b | .divide a b => a.fixedLiterals ++ b.fixedLiterals

def fixedCount (e : Expr ι) : ℕ := e.fixedLiterals.length

def addSubCount : Expr ι → ℕ
  | .atom _ | .fixed _ => 0
  | .add a b | .sub a b => a.addSubCount + b.addSubCount + 1
  | .mul a b | .divide a b => a.addSubCount + b.addSubCount

def heightCost (e : Expr ι) : ℕ := e.atomCount + e.fixedCount + e.addSubCount

def FixedBound (F : ℝ) (e : Expr ι) : Prop := ∀ c ∈ e.fixedLiterals, |(c : ℝ)| ≤ F

@[simp] theorem fixedBound_atom (F : ℝ) (i : ι) : (.atom i : Expr ι).FixedBound F := by
  simp [FixedBound, fixedLiterals]
@[simp] theorem fixedBound_fixed (F : ℝ) (c : ℤ) :
    (.fixed c : Expr ι).FixedBound F ↔ |(c : ℝ)| ≤ F := by
  simp [FixedBound, fixedLiterals]
@[simp] theorem fixedBound_add (F : ℝ) (a b : Expr ι) :
    (Expr.add a b).FixedBound F ↔ a.FixedBound F ∧ b.FixedBound F := by
  simp [FixedBound, fixedLiterals, List.mem_append, or_imp, forall_and]
@[simp] theorem fixedBound_sub (F : ℝ) (a b : Expr ι) :
    (Expr.sub a b).FixedBound F ↔ a.FixedBound F ∧ b.FixedBound F := by
  simp [FixedBound, fixedLiterals, List.mem_append, or_imp, forall_and]
@[simp] theorem fixedBound_mul (F : ℝ) (a b : Expr ι) :
    (Expr.mul a b).FixedBound F ↔ a.FixedBound F ∧ b.FixedBound F := by
  simp [FixedBound, fixedLiterals, List.mem_append, or_imp, forall_and]
@[simp] theorem fixedBound_divide (F : ℝ) (a b : Expr ι) :
    (Expr.divide a b).FixedBound F ↔ a.FixedBound F ∧ b.FixedBound F := by
  simp [FixedBound, fixedLiterals, List.mem_append, or_imp, forall_and]

theorem heightBudget_nonneg (e : Expr ι) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ e.heightBudget B := by
  induction e with
  | atom i => exact hB
  | fixed c => exact le_trans (by norm_num) (le_max_left _ _)
  | add a b ia ib | sub a b ia ib => exact mul_nonneg (mul_nonneg (by norm_num) ia) ib
  | mul a b ia ib | divide a b ia ib => exact mul_nonneg ia ib

theorem heightBudget_le_separate (e : Expr ι) {B F : ℝ} (hB : 1 ≤ B)
    (he : e.FixedBound F) :
    e.heightBudget B ≤ 2 ^ e.addSubCount * (max 1 F) ^ e.fixedCount * B ^ e.atomCount := by
  have hB0 : 0 ≤ B := by linarith
  have hF0 : 0 ≤ max 1 F := le_trans (by norm_num) (le_max_left _ _)
  induction e with
  | atom i => simp [heightBudget, addSubCount, fixedCount, fixedLiterals, atomCount]
  | fixed c =>
      simpa [heightBudget, addSubCount, fixedCount, fixedLiterals, atomCount] using
        max_le_max_left (1 : ℝ) ((fixedBound_fixed F c).mp he)
  | add a b ia ib | sub a b ia ib =>
      have ha : a.FixedBound F := fun c hc => he c (List.mem_append_left _ hc)
      have hb : b.FixedBound F := fun c hc => he c (List.mem_append_right _ hc)
      have hm := mul_le_mul (ia ha) (ib hb) (heightBudget_nonneg b hB0) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 by norm_num)
      convert hh using 1 <;>
        simp only [heightBudget, addSubCount, fixedCount, fixedLiterals, List.length_append,
          atomCount, pow_add, pow_one] <;> ring
  | mul a b ia ib | divide a b ia ib =>
      have ha : a.FixedBound F := fun c hc => he c (List.mem_append_left _ hc)
      have hb : b.FixedBound F := fun c hc => he c (List.mem_append_right _ hc)
      have hh := mul_le_mul (ia ha) (ib hb) (heightBudget_nonneg b hB0) (by positivity)
      convert hh using 1 <;>
        simp only [heightBudget, addSubCount, fixedCount, fixedLiterals, List.length_append,
          atomCount, pow_add]
      ring

theorem heightBudget_le_counts (e : Expr ι) {B F : ℝ} (hB : 1 ≤ B)
    (he : e.FixedBound F) :
    e.heightBudget B ≤ (2 * max 1 F) ^ (e.fixedCount + e.addSubCount) * B ^ e.atomCount := by
  have hF : 1 ≤ max 1 F := le_max_left _ _
  have h2 : (2 : ℝ) ≤ 2 * max 1 F := by linarith
  have hmax : max 1 F ≤ 2 * max 1 F := by linarith
  refine (heightBudget_le_separate e hB he).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    2 ^ e.addSubCount * max 1 F ^ e.fixedCount ≤
        (2 * max 1 F) ^ e.addSubCount * (2 * max 1 F) ^ e.fixedCount :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h2 _) (pow_le_pow_left₀ (by linarith) hmax _)
        (by positivity) (by positivity)
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem heightBudget_le_cost (e : Expr ι) {B F : ℝ} {C D : ℕ} (hB : 1 ≤ B)
    (he : e.FixedBound F) (hC : e.heightCost ≤ C) (hD : e.atomCount ≤ D) :
    e.heightBudget B ≤ (2 * max 1 F) ^ C * B ^ D := by
  refine (heightBudget_le_counts e hB he).trans ?_
  apply mul_le_mul
  · apply pow_le_pow_right₀ (by have := le_max_left (1 : ℝ) F; linarith)
    unfold heightCost at hC
    omega
  · exact pow_le_pow_right₀ hB hD
  · positivity
  · positivity

theorem fraction_eval_abs_le_counts (e : Expr ι) (x : ι → ℝ) {B F : ℝ} (hB : 1 ≤ B)
    (hx : ∀ i, |x i| ≤ B) (he : e.FixedBound F) :
    |MvPolynomial.eval₂ (Int.castRingHom ℝ) x e.numerator| ≤
        (2 * max 1 F) ^ (e.fixedCount + e.addSubCount) * B ^ e.atomCount ∧
    |MvPolynomial.eval₂ (Int.castRingHom ℝ) x e.denominator| ≤
        (2 * max 1 F) ^ (e.fixedCount + e.addSubCount) * B ^ e.atomCount :=
  ⟨(e.fraction_eval_abs_le x B hB hx).1.trans (e.heightBudget_le_counts hB he),
    (e.fraction_eval_abs_le x B hB hx).2.trans (e.heightBudget_le_counts hB he)⟩

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
