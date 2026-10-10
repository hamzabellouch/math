import OAI.NumberTheory.Ostmann.Conclusion.ParameterChoice

namespace OAI

noncomputable section
namespace Ostmann.Conclusion

theorem exists_actual_comparison_parameters (Csingle Ccov : ℝ) (k₀ : ℕ) :
    ∃BD Bz : ℝ,0≤BD ∧ 9≤Bz ∧ 200+Csingle+105≤BD ∧
      ∃k : ℕ,max 2 k₀≤k ∧ finalRate BD 200 Bz (Ccov+2) k < -66 := by
  obtain ⟨BD,Bz,hBD,hBz,hgap,k,hk,hrate⟩ :=
    exists_conclusion_parameters (Csingle+37) Ccov k₀
  exact ⟨BD,Bz,hBD,hBz,by linarith,k,hk,by linarith⟩

theorem actual_diagonal_exponential_le_required (k j : ℕ) (L : ℝ) :
    Real.exp (-66*(2:ℝ)^j*(bulkSize k L:ℝ)) ≤
      Real.exp (-65*(2:ℝ)^j*(bulkSize k L:ℝ)) := by
  apply Real.exp_le_exp.mpr
  have h : 0≤(2:ℝ)^j*(bulkSize k L:ℝ) := by positivity
  nlinarith

end Ostmann.Conclusion

end

end OAI
