import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNormalizedTerm

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma circuitD_dimension {d : ℕ} (F : Point d → ℝ) (x : Point d) :
    (d:ℝ)≤(circuitD F x)^2 := by
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  simpa only [Real.sq_sqrt (Nat.cast_nonneg d)] using h

lemma harmonicNormalizedTerm_mono (n : ℕ) {R z Z : ℝ} (hR : 0≤R) (hz : 0≤z) (hzZ : z≤Z) :
    harmonicNormalizedTerm n R z≤harmonicNormalizedTerm n R Z := by
  unfold harmonicNormalizedTerm
  rw [abs_of_nonneg hz,abs_of_nonneg (hz.trans hzZ)]
  gcongr

lemma kernelNormalizedTerm_mono (d k n N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h : ℝ) {z Z : ℝ} (hR : 0≤R) (hz : 0≤z) (hzZ : z≤Z) :
    kernelNormalizedTerm d k n N lam Ap Ah Lp r R h z≤
      kernelNormalizedTerm d k n N lam Ap Ah Lp r R h Z := by
  dsimp only [kernelNormalizedTerm]
  gcongr
  exact harmonicNormalizedTerm_mono n hR hz hzZ

lemma weighted_uniform_upper {ι : Type*} [Fintype ι] (a f : ι → ℝ) {B : ℝ}
    (ha : ∀i,0≤a i) (hf : ∀i,f i≤B) :
    (∑i,a i*f i)≤(∑i,a i)*B := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (ha i))

def kernelActionNormalizedBudget (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h ψ C J : ℝ) : ℝ :=
  let S := (∑i,|derivativeWeight (angleNodes m) i|)/ψ
  let V := (numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J
  let B := kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*m)
  600*(V*S*B)^2+2*S^2*((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
    (R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)

lemma kernelActionNormalizedBudget_nonneg (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h ψ C J : ℝ) (hR : 0≤R) : 0≤kernelActionNormalizedBudget d k n m N lam Ap Ah Lp r R h ψ C J := by
  unfold kernelActionNormalizedBudget
  positivity [harmonicCorrectionBudget_nonneg (m+1)]

theorem kernelActionRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R ρ h ψ C J : ℝ}
    (hr : 0≤r) (hr1 : r≤1) (hR : 0<R) (hh : 0≤h) (hψ : 0<ψ) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (k n m N : ℕ) :
    kernelActionRmsBudget F x lam Ap Ah Lp r R ρ h ψ C J k n m N ≤
      (((lam:ℝ)*r^2)*circuitD F x)^2*
        kernelActionNormalizedBudget d k n m N lam Ap Ah Lp r R h ψ C J := by
  let l := (lam:ℝ)*r^2
  let D := circuitD F x
  let S := (∑i,|derivativeWeight (angleNodes m) i|)/ψ
  let V := (numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J
  let B := kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*m)
  have hl0 : 0≤l := by positivity
  have hD : 0≤D := circuitD_nonneg F x
  have hV : 0≤V := by dsimp [V]; positivity [numericalContractionCoefficient_pos Ap Ah Lp,
    numericalErrorCoefficient_pos C J]
  have hS : 0≤S := by dsimp [S]; positivity
  have hw : (∑i,|derivativeWeight (angleNodes m) i/ψ|)=S := by
    simp only [abs_div,abs_of_pos hψ,←Finset.sum_div,S]
  have hb (i : Fin (m+1)) : kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h
      (ψ*angleNodes m i) C J k n N≤300*(V*l*B*D)^2 := by
    have hi0 : 0≤angleNodes m i := by dsimp [angleNodes]; positivity
    have hi1 : angleNodes m i≤(m:ℝ) := by dsimp [angleNodes]; exact_mod_cast Nat.le_of_lt_succ i.2
    have hz : 0≤ψ*angleNodes m i := mul_nonneg hψ.le hi0
    apply (kernelValueRmsBudget_normalized hF x Ap Ah Lp hr hr1 hR hh hz hC hJ hl hL hρ0 hρ1 k n N).trans
    have hmono := kernelNormalizedTerm_mono d k n N lam Ap Ah Lp r R h hR.le hz
      (mul_le_mul_of_nonneg_left hi1 hψ.le)
    have hbase : 0≤kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*angleNodes m i) := by
      unfold kernelNormalizedTerm
      positivity [probabilityNormalizedTerm_nonneg d k n hh,
        harmonicNormalizedTerm_nonneg (z:=ψ*angleNodes m i) n hR.le,
        numericalContractionCoefficient_pos Ap Ah Lp]
    change 300*(V*l*_*D)^2≤_
    gcongr
  have hsum := weighted_uniform_upper (fun i => |derivativeWeight (angleNodes m) i/ψ|)
    (fun i => kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h (ψ*angleNodes m i) C J k n N)
    (fun i => abs_nonneg _) hb
  rw [hw] at hsum
  have hnum := mul_le_mul_of_nonneg_left hsum (show 0≤2*S by positivity)
  have hdim := circuitD_dimension F x
  have hc : 0≤harmonicCorrectionBudget (m+1) := harmonicCorrectionBudget_nonneg (m+1)
  have hang : 2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((d*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))))≤
      2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((D^2*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
    gcongr
  unfold kernelActionRmsBudget
  rw [hw]
  calc
    _ ≤ 2*S*(S*(300*(V*l*B*D)^2))+2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
        ((D^2*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
      apply add_le_add
      · simpa only [mul_assoc] using hnum
      · exact hang
    _ = _ := by dsimp [kernelActionNormalizedBudget,V,B,S,l,D]; ring
end LogConcaveSampling

end

end

end OAI
