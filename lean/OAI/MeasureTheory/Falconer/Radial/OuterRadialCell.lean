import OAI.MeasureTheory.Falconer.Radial.OuterRadialWidths
import OAI.MeasureTheory.Falconer.Incidence.RadialZoomFiniteBalls
import OAI.MeasureTheory.Falconer.Radial.RadialZoomPruning

namespace OAI

/-! # Outer radial pruning for a full conditional law in an original source cell -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem outer_radial_cell_pruning {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ∀ᵐ y ∂μ,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1/(2:ℝ)^g →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^g*r)^q)) →
      (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let a : ℝ := 1/(2*D)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by positivity)).mpr; linarith
  have haD : a*D = 1/2 := by dsimp [a]; field_simp
  let e := radialZoom a ha.ne' (0 : Space d)
  obtain ⟨J,N₁,hN₁⟩ := outer_radial_interval_fixed_width (d := d)
    (by norm_num : (1:ℝ) ≤ 1) (mul_pos (by norm_num : (0:ℝ) < 2) hη₀) hq C
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (a^(-q))
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hgeom hball hcap
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hη0 : 0 < η := hη₀.trans_le hη
  have hK : 1 ≤ R^η := Real.one_le_rpow hR1 hη0.le
  have hcoeff : a^(-q) ≤ R^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 hη)
  have hcoeff' : R^η*a^(-q) ≤ R^(2*η) := by
    calc
      _ ≤ R^η*R^η := mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  have hballs := radialZoom_scaled_ball_bound μ ha ha1 hK
    (by positivity : 0 < (2:ℝ)^g) hq (by simp) (0 : Space d) hball
  have hdata : ∀ᵐ z ∂Measure.map e μ,
      (∀ᵐ y ∂Measure.map e μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
        ∀ x, (z,x) ∈ zoomPairSet e G → ‖y-x‖ ≤ 1) ∧
      (∀ j : ℕ, j ≤ v → Measure.map e μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((R^(2*η)*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (R^(2*η)*r^q)) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hgeom,hcap] with z hz hc
    refine ⟨?_,?_,?_⟩
    · rw [radialZoom_ae_iff μ ha]
      filter_upwards [hz] with y hy
      constructor
      · rw [norm_radialZoom_sub ha]
        calc
          _ ≤ a*(D/(2:ℝ)^g) := mul_le_mul_of_nonneg_left hy.1 ha.le
          _ = (1/2:ℝ)/(2:ℝ)^g := by rw [← mul_div_assoc,haD]
          _ < _ := div_lt_div_of_pos_right (by norm_num) (by positivity)
      · intro x hx
        let x₀ := e.symm x
        have hx' : (e.symm (e z),e.symm x) ∈ G := hx
        have hx₀ : (z,x₀) ∈ G := by simpa only [e.symm_apply_apply] using hx'
        have hxx : e x₀ = x := e.apply_symm_apply x
        rw [← hxx]
        change ‖radialZoom a ha.ne' 0 y-radialZoom a ha.ne' 0 x₀‖ ≤ _
        rw [norm_radialZoom_sub ha]
        exact (mul_le_mul_of_nonneg_left (hy.2 x₀ hx₀) ha.le).trans (by rw [haD]; norm_num)
    · intro j hj
      have hrj : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^j :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
      have hb := hballs (e z) (1/(2:ℝ)^j) (by positivity) hrj
      change Measure.map e μ (Metric.ball (e z) (1/(2:ℝ)^j)) ≤ _
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        _ = (R^η*a^(-q))*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) := by ring
        _ ≤ R^(2*η)*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) :=
          mul_le_mul_of_nonneg_right hcoeff' (by positivity)
        _ = _ := by ring
    · intro r hr hr1 u hu
      rw [radialZoom_reverse_cap ν ha _ z u r G hG]
      apply (hc r hr hr1 u hu).trans
      apply ENNReal.ofReal_le_ofReal
      have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (Real.rpow_nonneg hr0 q)
  have hdiag' : ∀ z x, (z,x) ∈ zoomPairSet e G → x ≠ z := by
    intro z x hx heq
    have hh := hdiag (e.symm z) (e.symm x) hx
    exact hh (congrArg e.symm heq)
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) (2*η)
    (by linarith) g v hgv hvN (Measure.map e μ) (Measure.map e ν) (zoomPairSet e G)
    (zoomPairSet_measurable e hG) hdiag' hdata
  have hbound' : ∀ p ∈ H, radialCollisionMass (Measure.map e μ) (C/(2:ℝ)^v) p ≤
      ENNReal.ofReal (R^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
    intro p hp
    simpa only [show 5*(2*η) = 10*η by ring] using hbound p hp
  exact radial_pruning_unzoom μ ν ha 0 G hG H hH hHG _ _ _ hdel hbound'

end Falconer

end OAI
