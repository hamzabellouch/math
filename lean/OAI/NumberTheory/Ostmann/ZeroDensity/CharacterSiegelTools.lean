import OAI.NumberTheory.PrimeGaps.SiegelBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterComplexification

namespace OAI

/-! # Bridges from the proved Siegel value bound to actual real zeros

The three reused character-analysis modules are the unchanged completed result
028 sources at f5371230bbb5024338caeeb3a6eaf46fb2cd4842. The derivative bridge
below specializes their regular Dirichlet-series bound near the line Re(s)=1.
-/

namespace Ostmann

open Filter Topology Complex

 theorem real_character_quadratic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    χ.IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hh := χ.unit_norm_eq_one u
    rw [Real.norm_eq_abs] at hh
    rcases abs_eq_abs.mp (hh.trans (abs_one.symm)) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (χ.map_nonunit hx)

 theorem character_deriv_small_power {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 - η / 2 ≤ s.re →
      ‖deriv χ.LFunction s‖ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η) := by
  obtain ⟨K, hK, h⟩ := LargePrimeGaps.regularSeries_deriv_norm_small_power hη hη1
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ s hs
  have he : LargePrimeGaps.regularSeries
      (LargePrimeGaps.positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually
      (lt_mem_nhds (by linarith : 0 < s.re))] with z hz
    exact LargePrimeGaps.regularSeries_character_eq hχ hz
  rw [← he.deriv_eq]
  have hb := h _ 0 (q + 1) (LargePrimeGaps.positiveCoefficients_zero _)
    (LargePrimeGaps.positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => LargePrimeGaps.discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

 theorem character_zero_value_bound {η K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hK : 0 < K) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hd : ∀ s : ℂ, 1 - η / 2 ≤ s.re →
      ‖deriv χ.LFunction s‖ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η))
    {β : ℝ} (hβ : 1 - η / 2 ≤ β) (hβ1 : β < 1) (hz : χ.LFunction (β : ℂ) = 0) :
    ‖χ.LFunction 1‖ ≤ (1 - β) * (K * 4 ^ (2 * η) * ((q : ℝ) + 2) ^ (2 * η)) := by
  have hbnd : ∀ s ∈ Metric.closedBall (1 : ℂ) (η / 2),
      ‖deriv χ.LFunction s‖ ≤ K * 4 ^ (2 * η) * ((q : ℝ) + 2) ^ (2 * η) := by
    intro s hs
    have hsD := Metric.mem_closedBall.mp hs
    have hsR : 1 - η / 2 ≤ s.re := by
      have hh := Complex.re_le_norm (1 - s)
      rw [Complex.sub_re, Complex.one_re, ← dist_eq_norm, dist_comm] at hh
      linarith
    have hsN : ‖s‖ ≤ 2 := by
      have hh : ‖s‖ ≤ dist s 1 + 1 := by simpa only [norm_one, sub_add_cancel, dist_eq_norm] using norm_add_le (s - 1) (1 : ℂ)
      linarith
    calc
      _ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η) := hd s hsR
      _ ≤ K * (((q : ℝ) + 2) * 4) ^ (2 * η) := by gcongr; nlinarith
      _ = _ := by rw [Real.mul_rpow (by positivity) (by norm_num)]; ring
  have hbetaMem : (β : ℂ) ∈ Metric.closedBall (1 : ℂ) (η / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : β - 1 < 0)]
    linarith
  have honeMem : (1 : ℂ) ∈ Metric.closedBall (1 : ℂ) (η / 2) := by
    simp only [Metric.mem_closedBall, dist_self]
    positivity
  have hh := (convex_closedBall (1 : ℂ) (η / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (DirichletCharacter.differentiable_LFunction hχ s)) hbnd hbetaMem honeMem
  rw [hz, sub_zero] at hh
  have hnorm : ‖(1 : ℂ) - (β : ℂ)‖ = 1 - β := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - β)]
  rw [hnorm] at hh
  nlinarith [hh]

end Ostmann

end OAI
