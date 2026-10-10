import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeDerivatives
import OAI.MeasureTheory.Falconer.Geometry.InactiveBinScales

namespace OAI

namespace PlanarFalconer

noncomputable def graphNonedgeDerivativeScale (N : ℕ) (sig u : ℝ) : ℝ :=
  (2:ℝ)^u * ((2:ℝ)^N)^(4*sig)

theorem graphNonedgeDerivativeScale_one_le (N : ℕ) {sig u : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) : 1 ≤ graphNonedgeDerivativeScale N sig u := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (by norm_num) hu
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)

theorem source_symbol_le_nonedge_scale (N L : ℕ) {sig u : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (hL : (L:ℝ) ≤ u+2*sig*(N:ℝ)) :
    sourceSymbolScale N sig L ≤ graphNonedgeDerivativeScale N sig u := by
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  unfold sourceSymbolScale graphNonedgeDerivativeScale
  rw [mul_max_of_nonneg _ _ (by positivity)]
  apply max_le
  · simp only [mul_one,dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [hu, mul_nonneg hsig hN]
  · rw [← Real.rpow_natCast (2:ℝ) L]
    simp only [dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig hN]

theorem graph_bin_le_nonedge_scale (N : ℕ) {sig t u c₀ : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (_hc : 0 < c₀)
    (ht : t ≤ u+2*sig*(N:ℝ)) :
    max 1 (graphAngularScale N sig t c₀)⁻¹ ≤
      max 1 c₀⁻¹ * graphNonedgeDerivativeScale N sig u := by
  have hE := graphNonedgeDerivativeScale_one_le N hsig hu
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hunc : (graphUncappedAngularScale N sig t)⁻¹ ≤ graphNonedgeDerivativeScale N sig u := by
    simp only [graphUncappedAngularScale,graphNonedgeDerivativeScale,dyadic_power_real,
      ← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_neg_one,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig hN]
  have hM : 1 ≤ max 1 c₀⁻¹ := le_max_left _ _
  have hEM : graphNonedgeDerivativeScale N sig u ≤ max 1 c₀⁻¹ * graphNonedgeDerivativeScale N sig u :=
    le_mul_of_one_le_left (zero_le_one.trans hE) hM
  apply max_le (hE.trans hEM)
  unfold graphAngularScale
  by_cases hcap : c₀ ≤ graphUncappedAngularScale N sig t
  · rw [min_eq_left hcap]
    exact (le_max_right 1 c₀⁻¹).trans (le_mul_of_one_le_right (zero_le_one.trans hM) hE)
  · rw [min_eq_right (le_of_not_ge hcap)]
    exact hunc.trans hEM

theorem graph_total_amplitude_scale (N L : ℕ) {sig t u c₀ : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (hc : 0 < c₀)
    (ht : t ≤ u+2*sig*(N:ℝ)) (hL : (L:ℝ) ≤ u+2*sig*(N:ℝ)) :
    1+4*max 1 (graphAngularScale N sig t c₀)⁻¹+sourceSymbolScale N sig L ≤
      (2+4*max 1 c₀⁻¹)*graphNonedgeDerivativeScale N sig u := by
  have hE := graphNonedgeDerivativeScale_one_le N hsig hu
  have hB := graph_bin_le_nonedge_scale N hsig hu hc ht
  have hD := source_symbol_le_nonedge_scale N L hsig hu hL
  nlinarith

theorem graph_nonedge_scale_gain (N : ℕ) (sig v p : ℝ) :
    graphNonedgeDerivativeScale N sig (v-p) /
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))) = ((2:ℝ)^N)^(-26*sig) := by
  simp only [graphNonedgeDerivativeScale,dyadic_power_real,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

end PlanarFalconer

end OAI
