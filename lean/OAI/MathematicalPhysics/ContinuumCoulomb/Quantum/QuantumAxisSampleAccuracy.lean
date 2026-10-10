import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSampleProgram

namespace OAI

/-! A linear precision schedule for the literal four-spin coupling sampler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample

theorem calibrated_error (a b : Fin 2) (k : ℕ) (t : ℚ) :
    |(calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      2*(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
  have h := coupling_error (2*k+6) k a b t
  have he : (2:ℝ)⁻¹^(2*k+6) = ((2:ℝ)⁻¹^k)^2/64 := by
    rw [show 2*k+6=k*2+6 by omega,pow_add,pow_mul]
    norm_num
    ring
  have heps : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have hs : Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^(2*k+6)) ≤
      (1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he,mul_pow]
    have hb : |(t:ℝ)|/12 ≤ (1+|(t:ℝ)|)^2 := by nlinarith [abs_nonneg (t:ℝ),sq_nonneg |(t:ℝ)|]
    calc
      _ = (|(t:ℝ)|/12)*((2:ℝ)⁻¹^k)^2 := by ring
      _ ≤ (1+|(t:ℝ)|)^2*((2:ℝ)⁻¹^k)^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  change |(coupling (2*k+6) k a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤ _
  apply h.trans
  have hp := mul_nonneg (abs_nonneg (t:ℝ)) heps
  linarith

theorem calibrated_nonneg (a b : Fin 2) (k : ℕ) (t : ℚ) : 0 ≤ calibrated a b (k,t) :=
  root_nonneg _ _

theorem calibrated_bound (a b : Fin 2) (k : ℕ) (t : ℚ) :
    |(calibrated a b (k,t):ℝ)| ≤ 5*(1+|(t:ℝ)|) := by
  have h := (abs_le.mp (calibrated_error a b k t)).2
  have hc := qmaFourCouplingSize_bound a b (t:ℝ)
  have he : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he' := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2*(1+|(t:ℝ)|))
  have hp : (0:ℝ) ≤ calibrated a b (k,t) := by exact_mod_cast calibrated_nonneg a b k t
  rw [abs_of_nonneg hp]
  linarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
