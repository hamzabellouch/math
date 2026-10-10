import OAI.Probability.FirstPassage.CompanionModel
import OAI.Probability.FirstPassage.LatticeLimitExtension
import OAI.Probability.FirstPassage.TimeConstantObligation
import OAI.Probability.LatticePassage.TimeConstantNorm

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable def actualSourceTimeConstant (v : Plane) : ℝ :=
  CompanionFPP.timeSeminorm (v 0,v 1)

theorem actualSourceTimeConstant_norm : TimeConstantNorm actualSourceTimeConstant where
  nonneg v := apply_nonneg _ _
  zero_iff v := by
    constructor
    · intro hv
      have he := CompanionFPP.actualTimeNorm.definite (v 0,v 1) hv
      ext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · rintro rfl
      exact map_zero _
  triangle v w := CompanionFPP.timeSeminorm.add_le' (v 0,v 1) (w 0,w 1)
  homogeneous a v := by
    change CompanionFPP.timeSeminorm (a • (v 0,v 1)) = _
    rw [map_smul_eq_mul,Real.norm_eq_abs]
    rfl

theorem actualSourceTimeConstant_bounds (v : Plane) :
    (Real.log 2/20)*‖v‖ ≤ actualSourceTimeConstant v ∧
      actualSourceTimeConstant v ≤ 2*‖v‖ := by
  constructor
  · exact (mul_le_mul_of_nonneg_left (plane_norm_le_coordinates v) (by positivity)).trans
      (CompanionFPP.timeSeminorm_linear_lower (v 0,v 1))
  · apply (CompanionFPP.timeSeminorm_bound (v 0,v 1)).trans
    have hh : ‖(v 0,v 1)‖ ≤ ‖v‖ := by
      rw [Prod.norm_def]
      exact max_le (plane_coordinate_le_norm v 0) (plane_coordinate_le_norm v 1)
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actualSourceTimeConstant_lattice_limits (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ z : Vertex,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z)/n) atTop
        (𝓝 (actualSourceTimeConstant (latticeEmbed z))) := by
  have hm : MeasurePreserving (fun ω => companionWeights (fun e => τ e ω)) P
      CompanionFPP.environmentLaw := ⟨measurable_companionWeights h.measurable,h.companionLaw⟩
  filter_upwards [hm.quasiMeasurePreserving.ae CompanionFPP.actualTimeNorm_hasTimeConstant] with ω hω
  intro z
  have hz := hω z
  simp only [companion_passageTime_eq] at hz
  have he (n : ℕ) : CompanionFPP.scaleVertex n z = n • z := by
    ext <;> simp [CompanionFPP.scaleVertex,nsmul_eq_mul]
  simp only [he] at hz
  exact hz

theorem actualSourceTimeConstant_all_real_limits (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ v : Plane,
      Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) 0 (latticeFloor (t • v))/t)
        atTop (𝓝 (actualSourceTimeConstant v)) := by
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n := by
    rw [ae_all_iff]
    intro k
    exact ae_eventually_passageTime_connections h (by positivity)
  filter_upwards [h.ae_positive,actualSourceTimeConstant_lattice_limits h,hc] with ω hp hr hc
  exact real_direction_limits_of_lattice_limits _ (fun e => (hp e).le)
    actualSourceTimeConstant actualSourceTimeConstant_norm hr hc

theorem actualSourceTimeConstant_isTimeConstant (h : ExponentialEnvironment P τ) :
    IsTimeConstant P τ actualSourceTimeConstant := by
  intro v
  filter_upwards [actualSourceTimeConstant_all_real_limits h] with ω hω
  exact hω v

theorem actualSourceTimeConstant_uniform_shape (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, UniformShape (fun e => τ e ω) actualSourceTimeConstant :=
  exponential_uniform_shape h actualSourceTimeConstant actualSourceTimeConstant_norm
    (actualSourceTimeConstant_isTimeConstant h)

theorem timeConstantExistence : TimeConstantExistenceTarget := by
  intro Ω _ P τ h
  exact ⟨actualSourceTimeConstant,actualSourceTimeConstant_norm,
    actualSourceTimeConstant_isTimeConstant h⟩

theorem actualSourceTimeConstant_unique (h : ExponentialEnvironment P τ)
    {μ : Plane → ℝ} (hμ : IsTimeConstant P τ μ) : μ=actualSourceTimeConstant :=
  isTimeConstant_unique h hμ (actualSourceTimeConstant_isTimeConstant h)

end PlanarFPP

end OAI
