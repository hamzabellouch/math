import OAI.MeasureTheory.Falconer.Radial.EndpointRadialPreparation
import OAI.MeasureTheory.Falconer.Estimates.EndpointSelectionLosses
import OAI.MeasureTheory.Falconer.Geometry.ChartFiniteScaleBounds
import OAI.MeasureTheory.Falconer.Angular.SmallGnomonicCap

namespace OAI

/-! # The radial endpoint costs from the original spherical direction law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {h : ℕ}

theorem endpoint_spherical_preparation (hLW : PublishedFiniteLoomisWhitney)
    {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) :
    ∃ ε c₁ c₂ : ℝ, 0 < ε ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ν : Measure (Sphere (h+3))) [IsProbabilityMeasure ν],
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^((h+1:ℕ):ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {v : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (v:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      let ν₀ := Measure.map gnomonicCoordinates ν
      ∃ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
              (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
            (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₂)) := by
  obtain ⟨ell,hell,hell'⟩ := exists_endpoint_radial_exponent h
  obtain ⟨e,b,f,c₀,c₁,c₂,he,_,_,_,hc₁,hc₂,N₁,hprep⟩ :=
    endpoint_radial_preparation hLW hζ hell hell' ha
  let ε := e/2
  have hε : 0 < ε := half_pos he
  obtain ⟨N₂,hconstant⟩ := Regularization.fixed_constant_absorbed hε ((4:ℝ)^((h+1:ℕ):ℝ))
  refine ⟨ε,c₁,c₂,hε,hc₁,hc₂,N₁+N₂,?_⟩
  intro N hN ν _ hcap hball hslab ν₀
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hL : 1 ≤ R^ε := Real.one_le_rpow hR1 hε.le
  have hεe : ε ≤ e := by dsimp [ε]; linarith
  have hloss : R^ε ≤ R^e := Real.rpow_le_rpow_of_exponent_le hR1 hεe
  have hchartloss : R^ε*4^((h+1:ℕ):ℝ) ≤ R^e := by
    calc
      _ ≤ R^ε*R^ε := mul_le_mul_of_nonneg_left (hconstant N (by omega)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; dsimp [ε]; ring
  have hpos : ∀ᵐ (w : Sphere (h+3)) ∂ν, 0 < (w:Space (h+3)) 0 := by
    filter_upwards [hcap] with w hw
    have hh := gnomonic_cap_first_coordinate w (hw.trans (by norm_num : (1/8:ℝ) ≤ 1/2))
    linarith
  have hsmall : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1/4 := small_gnomonic_cap_law ν hcap
  have hchartball : ∀ p : Space (h+2), ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν₀ (ball p r) ≤ ENNReal.ofReal (R^e*r^((h+1:ℕ):ℝ)) := by
    intro p r hr _
    have hh := gnomonic_dyadic_ball_bound ν N hL (by positivity) (by simp) hpos hball p
      (by simpa only [one_div] using hr)
    exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hchartloss
      (Real.rpow_nonneg (le_trans (by positivity) hr) _)))
  have hchartslab : ∀ w : Space (h+2), ‖w‖ = 1 → ∀ v r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν₀ {p | |inner ℝ w p-v| ≤ r} ≤ ENNReal.ofReal (R^e*r^ζ) := by
    intro w hw v r hr hr1
    obtain ⟨u,hu⟩ := gnomonicCoordinates_map_affine_plate ν hpos w v r hw
    exact (hu.trans (hslab u r hr hr1)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _)))
  obtain ⟨G,hG,_,_,hp,ht,_⟩ := hprep N (by omega) ν₀ hsmall hchartball hchartslab
  exact ⟨G,hG,hp,ht⟩

end Falconer

end OAI
