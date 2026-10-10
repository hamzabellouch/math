import OAI.Analysis.LipschitzHilbert.Fourier.MeasureClassKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The logarithmic restricted estimate is dominated by the summable
kernel of the actual dyadic support-measure classes. -/
noncomputable section
namespace LipschitzHilbert

def measureClassLogConstant : ℝ := (2+1/Real.log 2)^3

theorem measure_class_log_bound (m n : ℝ) (i j : ℤ)
    (hm : 0<m) (hn : 0<n)
    (hml : (2:ℝ)^i≤m) (hmu : m≤(2:ℝ)^(i+1))
    (hnl : (2:ℝ)^j≤n) (hnu : n≤(2:ℝ)^(j+1)) :
    ((1+|Real.log (m/n)|)^3)⁻¹≤measureClassLogConstant*measureClassKernel (i-j) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmlog := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<2) i) hml
  have hmulog := Real.log_le_log hm hmu
  have hnlog := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<2) j) hnl
  have hnulog := Real.log_le_log hn hnu
  simp only [Real.log_zpow,Int.cast_add,Int.cast_one] at hmlog hmulog hnlog hnulog
  have habs : |((i:ℝ)-(j:ℝ))*Real.log 2|≤|Real.log m-Real.log n|+Real.log 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [hmulog,hnlog,neg_abs_le (Real.log m-Real.log n)]
    · nlinarith only [hmlog,hnulog,le_abs_self (Real.log m-Real.log n)]
  rw [abs_mul,abs_of_pos hc,←Real.log_div hm.ne' hn.ne'] at habs
  have hcinv : Real.log 2*(1/Real.log 2)=1 := by field_simp
  have hC : 0<2+1/Real.log 2 := by positivity
  have hdenom : 1+|(i:ℝ)-(j:ℝ)|≤(2+1/Real.log 2)*(1+|Real.log (m/n)|) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have hnonneg := mul_nonneg hc.le (abs_nonneg (Real.log (m/n)))
    nlinarith only [habs,hcinv,hnonneg,abs_nonneg (Real.log (m/n))]
  have hnat : (Int.natAbs (i-j):ℝ)=|(i:ℝ)-(j:ℝ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+|(i:ℝ)-(j:ℝ)|) hdenom 3
  have hd : 0<(1+|Real.log (m/n)|)^3 := by positivity
  have hk : 0<(1+|(i:ℝ)-(j:ℝ)|)^3 := by positivity
  have hdiv : 1/(1+|Real.log (m/n)|)^3≤(2+1/Real.log 2)^3/(1+|(i:ℝ)-(j:ℝ)|)^3 := by
    apply (div_le_div_iff₀ hd hk).mpr
    simpa only [one_mul,mul_pow] using hpow
  simpa only [measureClassLogConstant,measureClassKernel,hnat,add_comm,div_eq_mul_inv,one_mul] using hdiv

end LipschitzHilbert

end

end OAI
