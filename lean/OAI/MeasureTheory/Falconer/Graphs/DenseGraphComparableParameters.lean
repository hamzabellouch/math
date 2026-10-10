import OAI.MeasureTheory.Falconer.Graphs.DenseGraphParameters

namespace OAI

/-! Additional polynomial room for comparable coordinate counts. -/
namespace Falconer

 theorem dense_graph_comparable_parameters {θ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      let R := Real.exp (θ*(N:ℝ)*Real.log 2)
      1 ≤ S ∧ S ≤ R ∧ 67108864*S^15 ≤ R ∧ R⁻¹ ≤ (S⁻¹)^2/64 := by
  obtain ⟨N0,hN0,hbounds⟩ := scalar_fixed_losses hθ
    (by norm_num : (0:ℝ) < 67108864) (by norm_num : (0:ℝ) < 64)
  let γ := θ/100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let R := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hSpos : 0 < S := Real.exp_pos _
  have hRpos : 0 < R := Real.exp_pos _
  have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
  have hS : 1 ≤ S := Real.one_le_exp_iff.mpr (by positivity)
  have hSR : S ≤ R := by
    apply Real.exp_le_exp.mpr
    dsimp [γ]
    nlinarith
  have hp (n : ℕ) (hn : (n:ℝ) ≤ 25) : S^n ≤ Real.exp ((θ/4)*(N:ℝ)*Real.log 2) := by
    rw [show S = Real.exp (γ*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp [γ]
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hθ.le hlog)
    nlinarith
  have h15 : 67108864*S^15 ≤ R :=
    (mul_le_mul_of_nonneg_left (hp 15 (by norm_num)) (by norm_num)).trans (hbounds N hN).1
  have h2 : 64*S^2 ≤ R :=
    (mul_le_mul_of_nonneg_left (hp 2 (by norm_num)) (by norm_num)).trans (hbounds N hN).2
  refine ⟨hS,hSR,h15,?_⟩
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 64*S^2) h2
  have he : (S⁻¹)^2/64 = 1/(64*S^2) := by field_simp
  change R⁻¹ ≤ (S⁻¹)^2/64
  rw [he]
  simpa only [one_div] using hi

end Falconer

end OAI
