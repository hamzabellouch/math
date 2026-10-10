import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarScaleChoice

namespace OAI

/-! Uniform contact calibration with a single fixed polynomial scale. -/

noncomputable section
namespace ContinuumCoulomb

/-- Every continuous distance-dependent target in a polynomial range is
attained by the actual amplified contact hopping at a permitted length. The
same fixed polynomial exponent works for every input size and every target
in that range. -/
theorem exists_uniform_planar_calibration_above (B : ℝ) (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ B ≤ (k : ℝ) ∧ ∀ N : ℝ, 2 ≤ N →
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧ ∀ q : ℝ → ℝ,
      ContinuousOn q (Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N))) →
      (∀ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N)), (N ^ A)⁻¹ ≤ q d ∧ q d ≤ N ^ A) →
      ∃ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N)), N ^ k * planarHopping d = q d := by
  obtain ⟨k, hk, hB, hscale⟩ := exists_planar_polynomial_brackets_above B A hε hε₁
  refine ⟨k, hk, hB, fun N hN => ?_⟩
  obtain ⟨hd, hlo, hhi⟩ := hscale N hN
  refine ⟨hd, fun q hq hbound => ?_⟩
  have hD : 0 ≤ (k : ℝ) * Real.log N :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hab : (1 - ε) * ((k : ℝ) * Real.log N) ≤
      (1 + ε) * ((k : ℝ) * Real.log N) := by nlinarith
  let F : ℝ → ℝ := fun d => N ^ k * planarHopping d - q d
  have hc : ContinuousOn F (Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
      ((1 + ε) * ((k : ℝ) * Real.log N))) :=
    (continuous_const.mul planarHopping_lipschitz.continuous).continuousOn.sub hq
  have h₀ : F ((1 + ε) * ((k : ℝ) * Real.log N)) ≤ 0 := by
    have h := hhi.trans (hbound _ ⟨hab, le_rfl⟩).1
    dsimp [F]
    linarith
  have h₁ : 0 ≤ F ((1 - ε) * ((k : ℝ) * Real.log N)) := by
    have h := (hbound _ ⟨le_rfl, hab⟩).2.trans hlo
    dsimp [F]
    linarith
  obtain ⟨d, hdmem, heq⟩ := intermediate_value_Icc' hab hc ⟨h₀, h₁⟩
  exact ⟨d, hdmem, sub_eq_zero.mp heq⟩

theorem exists_uniform_planar_calibration (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧ ∀ q : ℝ → ℝ,
      ContinuousOn q (Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N))) →
      (∀ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N)), (N ^ A)⁻¹ ≤ q d ∧ q d ≤ N ^ A) →
      ∃ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
        ((1 + ε) * ((k : ℝ) * Real.log N)), N ^ k * planarHopping d = q d := by
  obtain ⟨k, hk, _, h⟩ := exists_uniform_planar_calibration_above 0 A hε hε₁
  exact ⟨k, hk, h⟩

end ContinuumCoulomb

end

end OAI
