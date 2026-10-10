import OAI.NumberTheory.TotientAsymptotic.FordCostBudget
import OAI.NumberTheory.TotientAsymptotic.ComparisonExponentSaving

namespace OAI

/-! Restoring both residual tuples still leaves an exponential collision saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma recovery_prefactor_bound {n b d k : ℕ} {h Y : ℝ}
    (hh : 5 ≤ h) (hY : 0 ≤ Y) (hn : (n : ℝ) ≤ h) (hb : (b : ℝ) ≤ h)
    (hd : (d : ℝ) ≤ 2*Y/h^8) (hk : (k : ℝ) ≤ 2*Y/h^8) :
    (n+1 : ℝ)^(d+k)*(b+1 : ℝ)^d ≤ Real.exp (Y/(16*h^4)) := by
  have hnp : (0 : ℝ) < n+1 := by positivity
  have hbp : (0 : ℝ) < b+1 := by positivity
  have hln := Real.log_le_log hnp (show (n+1 : ℝ) ≤ h+1 by linarith)
  have hlb := Real.log_le_log hbp (show (b+1 : ℝ) ≤ h+1 by linarith)
  have hn0 : 0 ≤ Real.log (n+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hb0 : 0 ≤ Real.log (b+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) b])
  have hdk : ((d+k : ℕ) : ℝ) ≤ 2*(2*Y/h^8) := by push_cast; linarith
  have hleft := mul_le_mul hdk hln hn0 (by positivity : 0 ≤ 2*(2*Y/h^8))
  have hright := mul_le_mul hd hlb hb0 (by positivity : 0 ≤ 2*Y/h^8)
  have hcost : ((d+k : ℕ) : ℝ)*Real.log (n+1 : ℝ)+(d : ℝ)*Real.log (b+1 : ℝ) ≤ Y/(16*h^4) := by
    have hs := recovery_log_cost_small hh hY
    linarith
  have he1 : (n+1 : ℝ)^(d+k) = Real.exp ((d+k : ℕ)*Real.log (n+1 : ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hnp]
  have he2 : (b+1 : ℝ)^d = Real.exp ((d : ℝ)*Real.log (b+1 : ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hbp]
  rw [he1,he2,← Real.exp_add]
  exact Real.exp_le_exp.mpr hcost

lemma smooth_prefactor_bound {b : ℕ} {h Y T : ℝ}
    (hh : 2 ≤ h) (hb : (b : ℝ) ≤ h) (hY : 0 ≤ Y)
    (hT : 1 < T) (hZ : 0 ≤ B T) (hZu : B T ≤ 2*Y/h^18) :
    (Real.log T)^(20*(b : ℝ)*Real.log b+1) ≤ Real.exp (Y/(16*h^4)) := by
  rw [Real.rpow_def_of_pos (Real.log_pos hT)]
  apply Real.exp_le_exp.mpr
  have hc := smooth_log_cost_small hh hb hY hZ hZu
  change Real.log (Real.log T)*(20*(b : ℝ)*Real.log b+1) ≤ _
  change (20*(b : ℝ)*Real.log b+2)*Real.log (Real.log T) ≤ _ at hc
  change 0 ≤ Real.log (Real.log T) at hZ
  nlinarith

/-- A single class of fixed canceled primes, residual integer and grid has
this kernel after paying both missing-tuple and published Ford prefactors. -/
theorem ford_recovered_kernel {b n K D r : ℕ} {C y S h : ℝ} {Y U : ℕ → ℝ}
    (hC : 0 < C) (hy1 : 1 < y) (hy : 1 ≤ Real.log y) (hBy : 0 < B y)
    (hh : 5 ≤ h) (hn : (n : ℝ) ≤ h) (hb : (b : ℝ) ≤ h)
    (hlogB : Real.log (B y) ≤ 26*h)
    (hD : (D.primeFactorsList.length : ℝ) ≤ 2*B y/h^8)
    (hK : (K : ℝ) ≤ 2*B y/h^8)
    (hT : 1 < Y b) (hZ : 0 ≤ B (Y b)) (hZu : B (Y b) ≤ 2*B y/h^18)
    (hDr : 0 < D*r)
    (hE : -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+comparisonError b y S Y U ≤
      -1-1/(2*h^4)) :
    (n+1 : ℝ)^(D.primeFactorsList.length+K)*fordComparisonBound C b y S D r Y U ≤
      y/(D*r)/Real.log y*Real.exp (6*(|Real.log C|+26)*h^2-B y/(4*h^4)) := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have hp := ford_polynomial_prefactor hC hBy (by linarith) hb hlogB
  have hr := recovery_prefactor_bound hh hBy.le hn hb hD hK
  have hs := smooth_prefactor_bound (by linarith) hb hBy.le hT hZ hZu
  have hs0 := Real.rpow_nonneg (Real.log_nonneg hT.le) (20*(b : ℝ)*Real.log b+1)
  have he := comparison_log_power_saving hy hE
  have hdr : (0 : ℝ) < (D*r : ℕ) := by exact_mod_cast hDr
  have hscale : 0 ≤ y/(D*r) := div_nonneg hy0.le (by simpa using hdr.le)
  have hlog0 : 0 < Real.log y := zero_lt_one.trans_le hy
  calc
    _ = (y/(D*r))*((C*B y)^(6*b))*
        ((n+1 : ℝ)^(D.primeFactorsList.length+K)*(b+1 : ℝ)^D.primeFactorsList.length)*
        (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1)*
        (Real.log y)^(-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+comparisonError b y S Y U) := by
      unfold fordComparisonBound
      ring
    _ ≤ (y/(D*r))*Real.exp (6*(|Real.log C|+26)*h^2)*
        Real.exp (B y/(16*h^4))*Real.exp (B y/(16*h^4))*
        ((Real.log y)⁻¹*Real.exp (-(1/(2*h^4))*B y)) := by
      gcongr
    _ = y/(D*r)/Real.log y*Real.exp (6*(|Real.log C|+26)*h^2-3*B y/(8*h^4)) := by
      rw [show 6*(|Real.log C|+26)*h^2-3*B y/(8*h^4) =
        ((6*(|Real.log C|+26)*h^2+B y/(16*h^4))+B y/(16*h^4))+
          (-(1/(2*h^4))*B y) by ring,
        Real.exp_add,Real.exp_add,Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hfrac : B y/(4*h^4) ≤ 3*B y/(8*h^4) := by
        field_simp
        nlinarith
      linarith

end TotientAsymptotic

end

end OAI
