import OAI.Probability.RadialTransition.Main

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma support_ball_two_pressures_nearby {Q : Pressure} {x : Parameter} {ρ : ℝ}
    (hs : Metric.closedBall targetSlope pressureRadius ⊆
      supportSet (onParameters Q) positiveParameters x)
    (hρ : |ρ - 5*packingDensity/3| < pressureRadius/2) :
    pressureSupport Q (x 0) (x 1) (17*packingDensity/4-pressureRadius/2) ρ ∧
    pressureSupport Q (x 0) (x 1) (17*packingDensity/4+pressureRadius/2) ρ := by
  have hmem (z : ℝ) (hz : |z| ≤ pressureRadius/2) :
      parameter (17*packingDensity/4+z) ρ ∈
        Metric.closedBall targetSlope pressureRadius := by
    rw [Metric.mem_closedBall, dist_eq_norm, targetSlope, parameter_sub]
    have he : 17*packingDensity/4+z-17*packingDensity/4 = z := by ring
    rw [he]
    apply (parameter_norm_le _).trans
    simp only [parameter_zero, parameter_one]
    linarith
  have hpos := pressureRadius_pos
  have hs₁ := pressureSupport_iff.mpr
    (hs (hmem (-pressureRadius/2) (by rw [abs_of_nonpos (by linarith)]; linarith)))
  have hs₂ := pressureSupport_iff.mpr
    (hs (hmem (pressureRadius/2) (by rw [abs_of_pos (by positivity)])))
  simpa only [parameter_zero, parameter_one, sub_eq_add_neg, neg_div] using
    And.intro hs₁ hs₂

theorem densityInterval :
    ∃ (p : ℝ) (φ : Potential) (B C η βc : ℝ) (f : ℝ → ℝ → ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      0 < η ∧ Ioo (5*p/3 - η) (5*p/3 + η) ⊆ Ioi 0 ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧
      ∀ ρ ∈ Ioo (5*p/3 - η) (5*p/3 + η),
        IsCanonicalFreeEnergy φ ρ (fun β => f β ρ) ∧
        StrictTemperatureCorner (fun β => f β ρ) βc := by
  obtain ⟨t,b,ht,hb,hrow,x,hx,hsupport⟩ := exists_family_pressure_ball
  have ht0 : 0 < t := by linarith
  have had := iteration_admissible hb t
  let φ := familyPotential t (iterationMass b) (scaleRange b)
  let ρ₀ := 5*packingDensity/3
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; have := packingDensity_pos; positivity
  let η := min (pressureRadius/2) (ρ₀/2)
  have hη : 0 < η := lt_min (by have := pressureRadius_pos; positivity) (by positivity)
  have hηγ : η ≤ pressureRadius/2 := min_le_left _ _
  have hηρ : η ≤ ρ₀/2 := min_le_right _ _
  have hI : Ioo (ρ₀-η) (ρ₀+η) ⊆ Ioi 0 := by
    intro ρ hρ
    change 0 < ρ
    linarith [hρ.1]
  have hφ : Continuous φ := continuous_familyPotential had.1 had.2.1 had.2.2.1 t
  have hbd : IsBoundedPotential φ := bounded_familyPotential had.1 had.2.1 had.2.2.1 t
  have hrow' := admissible_row ht0.le had hrow
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, iterationMass b n)/2 ≤ t^2/16 := by
    nlinarith [sq_nonneg t]
  have hst : StableWith φ (t^2/2) :=
    stable_family_of_master ht0.le had.1 had.2.1 had.2.2.1 had.2.2.1 (fun _ => le_rfl) hrow'
  have hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0 := fun _ hr =>
    familyPotential_nonpos_outer had.1 had.2.1 ht hr
  have hlim (β d : ℝ) (hβ : 0 ≤ β) (hd : 0 ≤ d) :=
    (familyCanonicalThermo_spec ht had.1 had.2.1 had.2.2.1 hcoerc hβ hd).1
  let f := fun β ρ => t*canonicalThermo φ t β ρ/β
  have hβ : 0 < x 0 := phaseWindow_positive (by norm_num) hx
  have hβband : x 0 ∈ Icc (7/8:ℝ) (9/8) := by
    have hh := abs_le.mp (phaseWindow_coords hx).1
    constructor <;> linarith
  let C := t^2*(2:ℝ)^(3+1/32:ℝ)+
    t*bumpIntegral⁻¹*(∑' n, iterationMass b n*(scaleRange b n)^(1/32:ℝ))
  have hC : 0 < C := by
    have hw0 : 0 ≤ ∑' n, iterationMass b n*(scaleRange b n)^(1/32:ℝ) := by
      apply tsum_nonneg
      intro n
      exact mul_nonneg (had.1 n) (Real.rpow_nonneg (scaleRange_pos (by linarith) n).le _)
    have hbi := bumpIntegral_pos
    dsimp [C]
    positivity
  refine ⟨packingDensity,φ,t^2/2,C,η,x 0,f,packingDensity_pos,packingDensity_limit,
    hbd,hφ,by positivity,hC,hst,
    decay_familyPotential ht had.1 had.2.1 had.2.2.1 (iterationMass_weight_summable hb),
    hη,hI,hβband,?_⟩
  intro ρ hρI
  change ρ ∈ Ioo (ρ₀-η) (ρ₀+η) at hρI
  have hρ : 0 < ρ := hI hρI
  have hdensity : |ρ - 5*packingDensity/3| < pressureRadius/2 := by
    change |ρ - ρ₀| < pressureRadius/2
    exact abs_lt.mpr ⟨by linarith [hρI.1], by linarith [hρI.2]⟩
  have hf : IsCanonicalFreeEnergy φ ρ (fun β => f β ρ) :=
    family_free_energy ht hρ.le had.1 had.2.1 had.2.2.1 hcoerc
  have hdual (β : ℝ) (hβ : 0 < β) : canonicalThermo φ t β ρ =
      sSup (Set.range fun h : ℝ => h*ρ-grandPressure φ t β h) :=
    canonical_dual_sup hφ hbd hst ht0 hβ.le hρ hc (fun d hd => hlim β d hβ.le hd)
  have hconc : ConcaveOn ℝ (Ioi 0) (fun β => canonicalThermo φ t β ρ) :=
    canonicalThermo_concave hφ hbd ht0 hρ.le (fun β hβ => hlim β ρ hβ.le hρ.le)
  obtain ⟨hs₁,hs₂⟩ := support_ball_two_pressures_nearby hsupport hdensity
  exact ⟨hf, canonical_corner_of_pressure_supports hβ ht0
    (show 17*packingDensity/4-pressureRadius/2 <
      17*packingDensity/4+pressureRadius/2 by linarith [pressureRadius_pos])
    hdual hconc hs₁ hs₂⟩

end RadialTransition
end

end OAI
