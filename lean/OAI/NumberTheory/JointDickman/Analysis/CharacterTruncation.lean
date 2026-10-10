import OAI.NumberTheory.JointDickman.Analysis.CharacterConvolution

namespace OAI

/-! # Inserting the published character bound below the square-root cutoff -/

namespace JointDickman

open Finset

theorem smallCharacterConvolution_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (z Y D : ℝ) (V : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hY : 1 < Y) (hD : 0 ≤ D)
    (hbound : ∀ v ∈ Ioc 0 V,
      ‖squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * (Y / v) * (Real.log (Y / v)) ^ (-D))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / v)) :
    ‖∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
      squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) (neg_nonpos.mpr hD)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log (Y / v)) ^ (-D)) :=
      mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
        (hbound v hv) (norm_nonneg _) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log Y / 2) ^ (-D)) := by
      gcongr
    _ = _ := by ring

/-- Uniformity in the modulus is inherited from the published input.
The large-divisor remainder is the actual, already bounded convolution tail. -/
theorem roughCharacterSum_truncated
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
      9 ≤ Y → (V : ℝ) ^ 2 ≤ Y → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log Y / 2) ^ C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ E z Y‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
        ‖characterConvolutionTail χ E z ⌊Y⌋₊ V‖ := by
  obtain ⟨K, hK, hbound⟩ := hSW z hz C D hC hD
  refine ⟨K, hK, fun E Y V hY hV q _ hq χ hχ => ?_⟩
  obtain ⟨hVN, hsize⟩ := square_root_truncation_conditions hY hV
  have hY1 : 1 < Y := by linarith
  have hsmall := smallCharacterConvolution_bound χ E z Y D V hK hY1 hD
    (fun v hv => hbound (Y / v) (hsize v hv).1 q
      (hq.trans (Real.rpow_le_rpow (by positivity [Real.log_pos hY1])
        (hsize v hv).2 hC.le)) χ hχ)
    (fun v hv => (hsize v hv).2)
  rw [roughCharacterSum_split χ E z Y V hVN]
  exact (norm_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
