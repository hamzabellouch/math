import OAI.NumberTheory.TotientAsymptotic.LargeHeadRow
import OAI.NumberTheory.TotientAsymptotic.MovingSmoothMass
import OAI.NumberTheory.TotientAsymptotic.ExceptionalRowMass

namespace OAI

/-! Reciprocal mass for an arbitrary failed first row: the leading prime may be
small or large, and the preimage may have any length. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem failed_row_reciprocal_mass : ∃ A C F : ℝ,0 < A ∧ 0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    10000 ≤ B U → (8000/ω)^2 ≤ B U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ (ω/2)*B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ ∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (1+ω)*fordPrimeCoordinate n 0 < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ A/(Real.log U)^2+
      4*C*(Real.log 2)^(-1-coordinateDecay (ω/4) k)*(1+(coordinateDecay (ω/4) k)⁻¹)*
        Real.exp (-coordinateDecay (ω/4) k*B U) := by
  classical
  obtain ⟨A,hA,hsmooth⟩ := moving_smooth_reciprocal_mass
  obtain ⟨C,F,hC,hF,hrow⟩ := exceptional_row_reciprocal_mass
  refine ⟨A,C,F,hA,hC,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge Q hQ
  let S := Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧
    (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v)))
  let R := Q\S
  have hS := hsmooth U hU (by linarith only [hUexp,Real.exp_pos (Real.exp 1)]) hBU S (by
    intro v hv
    obtain ⟨hv,hn⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,hn⟩)
  have hR := hrow k (ω/2) U (by linarith) (by linarith) hU hUexp
    (by simpa only [show ω/2/2=ω/4 by ring] using hthreshold) hlarge R (by
      intro v hv
      obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hvU,n,hn,hφ,hfailed⟩ := hQ v hv
      have hv1 : (1:ℝ) < v := by linarith only [hvU,hU]
      have hBv := B_mono (show 1 < U by linarith only [hU]) hvU
      have hcut : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ) := by
        by_contra hh
        apply hnot
        exact Finset.mem_filter.mpr ⟨hv,n,hn,hφ,le_of_not_ge hh⟩
      refine ⟨hvU,⟨n,hn,hφ⟩,n,hn,hφ,?_⟩
      exact large_head_row_relative (by exact_mod_cast hv1)
        (by linarith only [hBU,hBv]) hω hω1 (hhead.trans hBv) hcut hfailed)
  have hsplit : (∑ v ∈ Q,(v:ℝ)⁻¹) = (∑ v ∈ S,(v:ℝ)⁻¹)+(∑ v ∈ R,(v:ℝ)⁻¹) := by
    have hsub : S ⊆ Q := Finset.filter_subset _ _
    have hh := Finset.sum_sdiff hsub (f:=fun v : ℕ => (v:ℝ)⁻¹)
    change (∑ v ∈ R,(v:ℝ)⁻¹)+(∑ v ∈ S,(v:ℝ)⁻¹) = _ at hh
    linarith only [hh]
  rw [hsplit]
  simpa only [show ω/2/2=ω/4 by ring] using add_le_add hS hR

end TotientAsymptotic

end

end OAI
