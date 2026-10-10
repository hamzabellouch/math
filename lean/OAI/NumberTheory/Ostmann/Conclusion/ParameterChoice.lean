import OAI.NumberTheory.Ostmann.Conclusion.FinalRateAbsorption
import OAI.NumberTheory.Ostmann.Conclusion.ScaleReserves

namespace OAI

noncomputable section
namespace Ostmann.Conclusion

theorem exists_conclusion_parameters (Cdiag Ccov : ℝ) (k₀ : ℕ) :
    ∃ BD Bz : ℝ, 0≤BD ∧ 9≤Bz ∧ 200+2*31+Cdiag+6≤BD ∧
      ∃k : ℕ, max 2 k₀≤k ∧ finalRate BD 200 Bz (Ccov+2) k < -2*31-4 := by
  let BD := max 0 (200+2*31+Cdiag+6)
  refine ⟨BD,9,le_max_left _ _,le_rfl,le_max_right _ _,?_⟩
  exact exists_depth_for_final_rate BD 200 9 (Ccov+2) 31 (max 2 k₀)

theorem exists_conclusion_reserves (Cdiag Ccov R0 : ℝ) (hR0 : 0<R0) (k₀ : ℕ) :
    ∃ BD Bz : ℝ, ∃k : ℕ, max 2 k₀≤k ∧ 0≤BD ∧ 9≤Bz ∧
      (∀L : ℝ,∀j : ℕ,diagonalExponent 200 BD Bz Cdiag k L j ≤
        -68*(2:ℝ)^j*(bulkSize k L:ℝ)) ∧
      (∀ᶠ L : ℝ in Filter.atTop,
        R0*(2*(frequencyBound 200 BD Bz k L k:ℝ)+1)*
          (((2:ℝ)^k)^(2*(2^k))*
            Real.exp ((2-(3/4:ℝ)*Real.log ((2:ℝ)^k))*(2:ℝ)^k*(bulkSize k L:ℝ))*
            Real.exp ((2:ℝ)^k*(initialGap 200 k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))+
            Real.exp (-(frequencyBudget 200 BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) ≤
          Real.exp (-63*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
  obtain ⟨BD,Bz,hBD,hBz,hgap,k,hk,hrate⟩ := exists_conclusion_parameters Cdiag Ccov k₀
  refine ⟨BD,Bz,k,hk,hBD,hBz,?_,?_⟩
  · intro L j
    have h := diagonalExponent_reserve (B:=31) (by omega : 1≤k) hBz hgap L j
    norm_num only at h
    simpa only [neg_mul] using h
  · have h := eventually_finalRate_absorption 200 BD Bz 31 R0 Ccov
      (by norm_num) hBD (by linarith) hR0 (by omega : 2≤k) hrate
    norm_num only at h
    simpa only [neg_mul] using h

end Ostmann.Conclusion

end

end OAI
