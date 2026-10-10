import OAI.NumberTheory.TotientAsymptotic.FailedRowTailBound
import OAI.NumberTheory.TotientAsymptotic.BoundedTotientMass

namespace OAI

/-! A complete reciprocal-mass bound for the residual values in a failed row. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem failed_row_total_mass : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    10000 ≤ B U → (8000/ω)^2 ≤ B U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ (ω/2)*B U → (coordinateDecay (ω/4) k)⁻¹ ≤ Real.exp (coordinateDecay (ω/4) k*B U) →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (1+ω)*fordPrimeCoordinate n 0 < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B U+4))^2) := by
  classical
  obtain ⟨P,hP,hsmall⟩ := bounded_totient_reciprocal_mass
  obtain ⟨A,C,F,hA,hC,hF,htail⟩ := failed_row_reciprocal_mass
  refine ⟨P+A+32*C,F,by positivity,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge hinv Q hQ
  let S : Finset ℕ := Q.filter (fun v : ℕ => (v:ℝ) ≤ U)
  let R : Finset ℕ := Q\S
  have hS := hsmall U (by linarith only [hU]) (by linarith only [hBU]) S (by
    intro v hv
    obtain ⟨hv,hvU⟩ := Finset.mem_filter.mp hv
    obtain ⟨n,hn,hφ,_⟩ := hQ v hv
    exact ⟨⟨n,hn,hφ⟩,hvU⟩)
  have hR := htail k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge R (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    have hUv : U ≤ (v:ℝ) := by
      by_contra hh
      exact hnot (Finset.mem_filter.mpr ⟨hv,le_of_not_ge hh⟩)
    exact ⟨hUv,hQ v hv⟩)
  have hδ := coordinate_decay_bounds (k:=k) (show 0 ≤ ω/4 by linarith) (show ω/4 ≤ 1 by linarith)
  have hc := row_tail_coefficient_bound (coordinate_decay_pos (show 0 < ω/4 by linarith) k)
    (hδ.2.1.trans (by norm_num)) hinv
  have hc' := mul_le_mul_of_nonneg_left hc hC.le
  have hlog : 1 ≤ Real.log U := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ) ≤ U by linarith only [hU])
    linarith [Real.log_three_gt_d9]
  have hA' : A/(Real.log U)^2 ≤ A := by
    apply (div_le_iff₀ (by positivity : 0 < (Real.log U)^2)).mpr
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) hlog) hA.le
    simpa only [mul_one] using hh
  have hE : 1 ≤ Real.exp (10*(Real.log (B U+4))^2) := Real.one_le_exp (by positivity)
  have hbound : (∑ v ∈ R,(v:ℝ)⁻¹) ≤
      (A+32*C)*Real.exp (10*(Real.log (B U+4))^2) := by
    have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ A+32*C by positivity)
    nlinarith only [hR,hc',hA',hh]
  have hsplit := Finset.sum_sdiff (show S ⊆ Q from Finset.filter_subset _ _)
    (f:=fun v : ℕ => (v:ℝ)⁻¹)
  change (∑ v ∈ R,(v:ℝ)⁻¹)+(∑ v ∈ S,(v:ℝ)⁻¹)=(∑ v ∈ Q,(v:ℝ)⁻¹) at hsplit
  nlinarith only [hS,hbound,hsplit]

end TotientAsymptotic

end

end OAI
