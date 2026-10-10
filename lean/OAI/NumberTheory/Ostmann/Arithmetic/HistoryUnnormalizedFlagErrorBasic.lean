import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalizedExact
import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError

def errorBudget (A J D H atom mass : ℝ) (n : ℕ) : ℝ :=
  A*J*(D*atom*mass^(n-1)*mass+atom*H*mass^n)

theorem errorBudget_le {A J D H atom mass Q : ℝ} {n : ℕ}
    (_hA : 0 ≤ A) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (ha : 0 ≤ atom) (hm : 1 ≤ mass) (hQ : 0 ≤ Q)
    (hAQ : A ≤ Q) (hJQ : J ≤ Q) (hDQ : D ≤ Q) (hHQ : H ≤ Q) :
    errorBudget A J D H atom mass n ≤ 2*Q^3*atom*mass^(n+1) := by
  have hm0 : 0 ≤ mass := zero_le_one.trans hm
  have hp : mass^(n-1)*mass ≤ mass^(n+1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hm (by omega)
  have hp' : mass^n ≤ mass^(n+1) := pow_le_pow_right₀ hm (by omega)
  have h₁ : D*atom*mass^(n-1)*mass ≤ Q*atom*mass^(n+1) := by
    calc
      _ = (D*atom)*(mass^(n-1)*mass) := by ring
      _ ≤ (Q*atom)*mass^(n+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hDQ ha) hp (by positivity) (mul_nonneg hQ ha)
  have h₂ : atom*H*mass^n ≤ Q*atom*mass^(n+1) := by
    calc
      _ = (H*atom)*mass^n := by ring
      _ ≤ (Q*atom)*mass^(n+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hHQ ha) hp' (by positivity) (mul_nonneg hQ ha)
  have hAJ : A*J ≤ Q*Q := mul_le_mul hAQ hJQ hJ hQ
  unfold errorBudget
  calc
    _ ≤ (Q*Q)*(Q*atom*mass^(n+1)+Q*atom*mass^(n+1)) :=
      mul_le_mul hAJ (add_le_add h₁ h₂) (by positivity) (mul_nonneg hQ hQ)
    _ = _ := by ring

theorem polynomial_mass_exponent_le {L N R T : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hR : 0 ≤ R) (_hT : 0 ≤ T)
    (hn : (n:ℝ) ≤ R*(L+1)) :
    1+3*(T*(L+1)^2*Real.exp ((11/10000:ℝ)*L))+N*L+
      ((n+1:ℕ):ℝ)*(N*L) ≤
      (3*T+N*(R+2)+1)*(L+1)^2*Real.exp ((11/10000:ℝ)*L) := by
  have he : 1 ≤ Real.exp ((11/10000:ℝ)*L) := Real.one_le_exp (by positivity)
  have hsq : 1 ≤ (L+1)^2 := by nlinarith
  have hm : (n:ℝ)+2 ≤ (R+2)*(L+1) := by nlinarith
  have hl : L ≤ L+1 := by linarith
  have hprod := mul_le_mul hm hl hL (by positivity : 0 ≤ (R+2)*(L+1))
  have hprodN := mul_le_mul_of_nonneg_left hprod hN
  have hbase : 1+N*L+((n+1:ℕ):ℝ)*(N*L) ≤ (N*(R+2)+1)*(L+1)^2 := by
    simp only [Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hbase' := le_mul_of_one_le_right
    (by positivity : 0 ≤ (N*(R+2)+1)*(L+1)^2) he
  nlinarith

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
