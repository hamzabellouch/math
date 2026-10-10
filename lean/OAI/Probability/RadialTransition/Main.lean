import OAI.Probability.RadialTransition.InfiniteBall

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma canonical_dual_sup {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β ρ : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β) (hρ : 0 < ρ)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) :
    canonicalThermo φ t β ρ = sSup (Set.range fun h : ℝ => h*ρ-grandPressure φ t β h) := by
  obtain ⟨h,he,hle⟩ := (canonical_grand_duality hφ hb hstable ht hβ hc hlim).2 ρ hρ
  apply le_antisymm
  · rw [he]
    apply le_csSup
    · exact ⟨canonicalThermo φ t β ρ,fun v ⟨j,hj⟩ => hj ▸ hle j⟩
    · exact ⟨h,rfl⟩
  · exact csSup_le (Set.range_nonempty _) (fun v ⟨j,hj⟩ => hj ▸ hle j)

lemma support_ball_two_pressures {Q : Pressure} {x : Parameter}
    (hs : Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters Q) positiveParameters x) :
    pressureSupport Q (x 0) (x 1) (17*packingDensity/4-pressureRadius/2) (5*packingDensity/3) ∧
    pressureSupport Q (x 0) (x 1) (17*packingDensity/4+pressureRadius/2) (5*packingDensity/3) := by
  have hp := pressureRadius_pos
  have hmem (z : ℝ) (hz : |z|≤pressureRadius) : parameter (17*packingDensity/4+z) (5*packingDensity/3) ∈
      Metric.closedBall targetSlope pressureRadius := by
    rw [Metric.mem_closedBall,dist_eq_norm,targetSlope,parameter_sub,sub_self]
    have he : 17*packingDensity/4+z-17*packingDensity/4=z := by ring
    rw [he,parameter_horizontal_norm]
    exact hz
  have hs₁ := pressureSupport_iff.mpr (hs (hmem (-pressureRadius/2) (by rw [abs_of_nonpos (by linarith)]; linarith)))
  have hs₂ := pressureSupport_iff.mpr (hs (hmem (pressureRadius/2) (by rw [abs_of_pos (by positivity)]; linarith)))
  simpa only [parameter_zero,parameter_one,sub_eq_add_neg,neg_div] using And.intro hs₁ hs₂

lemma family_free_energy {t ρ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, a n)/2 ≤ t^2/16) :
    IsCanonicalFreeEnergy (familyPotential t a R) ρ
      (fun β => t*canonicalThermo (familyPotential t a R) t β ρ/β) := by
  intro β hβ
  have ht0 : 0 < t := by linarith
  have hlim := ((familyCanonicalThermo_spec ht ha hR hs hcoerc hβ.le hρ).1.comp
    (floor_tendsto_thermodynamicFilter hρ)).const_mul t |>.div_const β
  convert hlim using 1
  ext L
  dsimp only [Function.comp_apply,finiteCanonical]
  field_simp

theorem main :
    ∃ (p : ℝ) (φ : Potential) (B C : ℝ) (f : ℝ → ℝ) (βc : ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      IsCanonicalFreeEnergy φ (5*p/3) f ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧ StrictTemperatureCorner f βc := by
  obtain ⟨t,b,ht,hb,hrow,x,hx,hsupport⟩ := exists_family_pressure_ball
  have ht0 : 0 < t := by linarith
  have had := iteration_admissible hb t
  let φ := familyPotential t (iterationMass b) (scaleRange b)
  let ρ := 5*packingDensity/3
  have hρ : 0 < ρ := by dsimp [ρ]; have := packingDensity_pos; positivity
  have hφ : Continuous φ := continuous_familyPotential had.1 had.2.1 had.2.2.1 t
  have hbd : IsBoundedPotential φ := bounded_familyPotential had.1 had.2.1 had.2.2.1 t
  have hrow' := admissible_row ht0.le had hrow
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, iterationMass b n)/2 ≤ t^2/16 := by
    nlinarith [sq_nonneg t]
  have hst : StableWith φ (t^2/2) := stable_family_of_master ht0.le had.1 had.2.1 had.2.2.1 had.2.2.1 (fun _ => le_rfl) hrow'
  have hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0 := fun _ hr => familyPotential_nonpos_outer had.1 had.2.1 ht hr
  have hlim (β d : ℝ) (hβ : 0≤β) (hd : 0≤d) := (familyCanonicalThermo_spec ht had.1 had.2.1 had.2.2.1 hcoerc hβ hd).1
  let f := fun β => t*canonicalThermo φ t β ρ/β
  have hf : IsCanonicalFreeEnergy φ ρ f := family_free_energy ht hρ.le had.1 had.2.1 had.2.2.1 hcoerc
  have hβ : 0 < x 0 := phaseWindow_positive (by norm_num) hx
  have hβband : x 0 ∈ Icc (7/8:ℝ) (9/8) := by
    have hh := abs_le.mp (phaseWindow_coords hx).1
    constructor <;> linarith
  have hdual (β : ℝ) (hβ : 0 < β) : canonicalThermo φ t β ρ =
      sSup (Set.range fun h : ℝ => h*ρ-grandPressure φ t β h) :=
    canonical_dual_sup hφ hbd hst ht0 hβ.le hρ hc (fun d hd => hlim β d hβ.le hd)
  have hconc : ConcaveOn ℝ (Ioi 0) (fun β => canonicalThermo φ t β ρ) :=
    canonicalThermo_concave hφ hbd ht0 hρ.le (fun β hβ => hlim β ρ hβ.le hρ.le)
  obtain ⟨hs₁,hs₂⟩ := support_ball_two_pressures hsupport
  have hcorner : StrictTemperatureCorner f (x 0) := canonical_corner_of_pressure_supports hβ ht0
    (show 17*packingDensity/4-pressureRadius/2 < 17*packingDensity/4+pressureRadius/2 by linarith [pressureRadius_pos]) hdual hconc hs₁ hs₂
  let C := t^2*(2:ℝ)^(3+1/32:ℝ)+t*bumpIntegral⁻¹*(∑' n, iterationMass b n*(scaleRange b n)^(1/32:ℝ))
  have hC : 0 < C := by
    have hw0 : 0≤∑' n, iterationMass b n*(scaleRange b n)^(1/32:ℝ) := by
      apply tsum_nonneg
      intro n
      exact mul_nonneg (had.1 n) (Real.rpow_nonneg (scaleRange_pos (by linarith) n).le _)
    have hbi := bumpIntegral_pos
    dsimp [C]
    positivity
  exact ⟨packingDensity,φ,t^2/2,C,f,x 0,packingDensity_pos,packingDensity_limit,hbd,hφ,
    by positivity,hC,hst,decay_familyPotential ht had.1 had.2.1 had.2.2.1 (iterationMass_weight_summable hb),
    hf,hβband,hcorner⟩

end RadialTransition
end

end OAI
