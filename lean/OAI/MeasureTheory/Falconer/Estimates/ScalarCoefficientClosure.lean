import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientMul
import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientNeg

namespace OAI

/-! The finite additive and multiplicative closure used in the scalar
sum-product argument. Each stage has an explicit coefficient radius. -/
namespace Falconer
open scoped Pointwise

noncomputable def scalarCoefficientClosure (S : Finset ℝ) : ℕ → Finset ℝ
  | 0 => S
  | n+1 => let T := scalarCoefficientClosure S n
    (T ∪ -T) ∪ ((T+T) ∪ (T*T))

def scalarCoefficientRadius (M : ℕ) : ℕ → ℕ
  | 0 => M+1
  | n+1 => 2*(scalarCoefficientRadius M n)^2

theorem scalarCoefficientRadius_pos (M n : ℕ) : 0 < scalarCoefficientRadius M n := by
  induction n with
  | zero => simp [scalarCoefficientRadius]
  | succ n ih => simp only [scalarCoefficientRadius]; positivity

theorem scalarCoefficientClosure_bound (S : Finset ℝ) (M : ℕ)
    (hS : ∀ c ∈ S, |c| ≤ M) (n : ℕ) :
    ∀ c ∈ scalarCoefficientClosure S n, |c| ≤ scalarCoefficientRadius M n := by
  induction n with
  | zero =>
    intro c hc
    exact (hS c hc).trans (by simp [scalarCoefficientRadius])
  | succ n ih =>
    intro c hc
    let R : ℝ := scalarCoefficientRadius M n
    have hR : 1 ≤ R := by
      change (1 : ℝ) ≤ (scalarCoefficientRadius M n : ℝ)
      exact_mod_cast Nat.succ_le_of_lt (scalarCoefficientRadius_pos M n)
    have hrad : (scalarCoefficientRadius M (n+1) : ℝ) = 2*R^2 := by
      simp [scalarCoefficientRadius,R]
    rw [hrad]
    have hstep : R ≤ 2*R^2 := by nlinarith
    change c ∈ (scalarCoefficientClosure S n ∪ -scalarCoefficientClosure S n) ∪
      ((scalarCoefficientClosure S n+scalarCoefficientClosure S n) ∪
        (scalarCoefficientClosure S n*scalarCoefficientClosure S n)) at hc
    rcases Finset.mem_union.mp hc with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (ih c h).trans hstep
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_neg.mp h
        simpa only [abs_neg] using (ih x hx).trans hstep
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp h
        have haa := ih a ha
        have hbb := ih b hb
        exact (abs_add_le a b).trans (by change |a| ≤ R at haa; change |b| ≤ R at hbb; nlinarith)
      · obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp h
        rw [abs_mul]
        have hh := mul_le_mul (ih a ha) (ih b hb) (abs_nonneg _) (by positivity)
        exact hh.trans (by change R*R ≤ 2*R^2; nlinarith)

end Falconer

end OAI
