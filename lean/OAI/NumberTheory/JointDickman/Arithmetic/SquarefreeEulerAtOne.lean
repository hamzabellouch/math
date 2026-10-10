import OAI.NumberTheory.JointDickman.Analysis.SquarefreeEulerAnalytic

namespace OAI

/-! # The analytic Euler factor at the leading singularity -/
namespace JointDickman

 theorem squarefreePrimeLog_one {z : ℝ} (hz : 0 ≤ z) (p : Nat.Primes) :
    squarefreePrimeLog z 1 p = (Real.log (squarefreeEulerFactor z p.val) : ℂ) := by
  have hp0 : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hp1 : (1:ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hsub : 0 < 1-1/(p.val:ℝ) := by
    have := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1+z/(p.val:ℝ) := by positivity
  rw [squarefreeEulerFactor,Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',Real.log_rpow hsub]
  rw [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_log hadd.le,Complex.ofReal_log hsub.le]
  simp only [squarefreePrimeLog,squarefreeEulerLog,Complex.cpow_neg_one]
  push_cast
  simp only [div_eq_mul_inv,one_mul]

 theorem squarefreeEuler_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun p : Nat.Primes => Real.log (squarefreeEulerFactor z p.val)) := by
  convert! (primeEulerFactor_log_summable hz hz1).subtype Nat.Prime using 1
  ext p
  simp only [Function.comp_def,primeEulerFactor,p.property,ite_true]

 theorem squarefreeAnalyticFactor_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    squarefreeAnalyticFactor z 1 = (∏' p : Nat.Primes, squarefreeEulerFactor z p.val : ℝ) := by
  have heq : squarefreeLogFactor z 1 = (∑' p : Nat.Primes, Real.log (squarefreeEulerFactor z p.val) : ℝ) := by
    rw [squarefreeLogFactor,Complex.ofReal_tsum]
    exact tsum_congr (squarefreePrimeLog_one hz)
  rw [squarefreeAnalyticFactor,heq,← Complex.ofReal_exp,
    Real.rexp_tsum_eq_tprod (fun p : Nat.Primes => squarefreeEulerFactor_pos hz p.property)
      (squarefreeEuler_log_summable hz hz1)]

 theorem squarefreeAnalyticFactor_one_gamma {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeAnalyticFactor z 1 = (squarefreeLeadingConstant z * Real.Gamma z : ℝ) := by
  rw [squarefreeAnalyticFactor_one hz.le hz1,squarefreeLeadingConstant,
    div_mul_cancel₀ _ (Real.Gamma_pos_of_pos hz).ne']
  rfl

end JointDickman

end OAI
