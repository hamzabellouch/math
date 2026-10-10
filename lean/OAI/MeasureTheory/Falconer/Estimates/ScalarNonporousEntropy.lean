import OAI.MeasureTheory.Falconer.Estimates.ScalarActualPorousGain

namespace OAI

/-! Logarithmic form of the fixed-fold sumset bound, and the resulting
 quantitative supply of porous blocks for a set below full dimension. -/
namespace Falconer

 theorem scalar_nonporous_log_bound {bad copies J q : ℕ} {K : ℝ}
    (hK : 0 < K) (hq : 0 < q)
    (h : ((J+1)^bad:ℝ) ≤ (copies+2)*(2*K)^copies*(q:ℝ)) :
    (bad:ℝ)*Real.log (J+1:ℝ) ≤
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*K)+Real.log (q:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (J+1:ℝ)^bad) h
  rw [Real.log_pow,Real.log_mul (by positivity) hqR.ne',
    Real.log_mul (by positivity) (by positivity),Real.log_pow] at hh
  exact hh

 theorem scalar_porous_fraction {M bad B : ℕ} {κ cost size Jlog : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Jlog)
    (hcost : cost ≤ (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hsize : size ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hcount : (bad:ℝ)*Jlog ≤ cost+size) :
    (bad:ℝ) ≤ (1-κ/2)*(M:ℝ) := by
  let x : ℝ := (B:ℝ)*Real.log 2
  have hx : 0 < x := mul_pos (by exact_mod_cast hB) (Real.log_pos (by norm_num))
  have hc : 0 < (1-κ/4)*x := mul_pos (by linarith) hx
  have hlow := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg bad)
  have hpre : (bad:ℝ)*((1-κ/4)*x) ≤ (1-3*κ/4)*(M:ℝ)*x := by
    dsimp [x] at *
    nlinarith
  have hcoef : (1-3*κ/4)*(M:ℝ) ≤ ((1-κ/2)*(M:ℝ))*(1-κ/4) := by
    have hs : 0 ≤ κ^2*(M:ℝ) := mul_nonneg (pow_nonneg hκ.le 2) (Nat.cast_nonneg M)
    nlinarith
  have hmain : (bad:ℝ)*((1-κ/4)*x) ≤ ((1-κ/2)*(M:ℝ))*((1-κ/4)*x) := by
    calc
      _ ≤ (1-3*κ/4)*(M:ℝ)*x := hpre
      _ ≤ (((1-κ/2)*(M:ℝ))*(1-κ/4))*x := mul_le_mul_of_nonneg_right hcoef hx.le
      _ = _ := by ring
  exact le_of_mul_le_mul_right hmain hc

namespace Regularization

 theorem scalar_porous_count_from_entropy {B M C : ℕ} (k n : ℕ → ℕ)
    {κ cost size Jlog : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Jlog)
    (hcost : cost ≤ (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hsize : size ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hcount : ((scalarNonporousLevels M B C k n).card:ℝ)*Jlog ≤ cost+size) :
    (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ) := by
  have hh := scalar_porous_fraction hκ hκ1 hB hJ hcost hsize hcount
  have hc : ((scalarPorousLevels M B C k n).card:ℝ)+
      ((scalarNonporousLevels M B C k n).card:ℝ) = (M:ℝ) := by
    exact_mod_cast scalar_porous_count M B C k n
  nlinarith

end Regularization
end Falconer

end OAI
