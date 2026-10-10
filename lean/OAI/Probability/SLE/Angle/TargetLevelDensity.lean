import OAI.Probability.SLE.Angle.TargetLevelTime
import OAI.Probability.SLE.Angle.TargetDiskRadius
import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel

namespace OAI

/-! The prescribed finite-level density is the actual normalized stopped
Green density, with no change to its finite/infinite-time convention. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

private lemma alpha_eq (κ : ℝ) (_hκ : 0 < κ) : α κ=codimension κ := by
  dsimp only [α,d,a,codimension,dimension]
  field_simp [_hκ.ne']
  ring

private lemma p_eq (κ : ℝ) : p κ=greenExponent κ := by
  dsimp only [p,a,greenExponent]
  ring

lemma disk_center_sin_arg (θ : ℝ) :
    Real.sin (Complex.arg (diskMapInv θ 0))=Real.sin θ := by
  have hz : diskMapInv θ 0=Complex.exp (θ*Complex.I) := by simp [diskMapInv]
  rw [hz,Complex.sin_arg,Complex.norm_exp_ofReal_mul_I,div_one,
    Complex.exp_ofReal_mul_I_im]

lemma levelDensity_eq_stoppedGreen
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    levelDensity κ θ b ℓ =
      stoppedGreen κ U γ G (diskMapInv θ 0) (4*ℓ/κ)/initialGreen κ (diskMapInv θ 0) := by
  let z := diskMapInv θ 0
  let u := 4*ℓ/κ
  let τ := radiusLevelTime γ G z u
  have hzH : z ∈ upperHalfPlane := diskMapInv_maps hθ (by simp)
  have hc : 0 < 2*z.im := mul_pos (by norm_num) hzH
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hA : (2*z.im)^(-codimension κ) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hD : (Real.sin θ)^greenExponent κ ≠ 0 := (Real.rpow_pos_of_pos hsin _).ne'
  have htime := levelTime_eq_radiusLevelTime κ hκ b U hUc γ G F hw hU θ ℓ hℓ
  change levelTime κ θ b ℓ=ENNReal.ofReal κ*τ at htime
  by_cases hfin : τ<∞
  · obtain ⟨T,hT,hTR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u hfin
    have hτT : τ=(T:ℝ≥0∞) := radiusLevelTime_eq_of_live_level hUc hw z u T hT hTR
    have htarget : levelTime κ θ b ℓ=ENNReal.ofReal (κ*(T:ℝ)) := by
      rw [htime,hτT,ENNReal.ofReal_mul hκ.le,ENNReal.ofReal_coe_nnreal]
    have htargetfin : levelTime κ θ b ℓ<∞ := by rw [htarget]; exact ENNReal.ofReal_lt_top
    have htargreal : (levelTime κ θ b ℓ).toReal=κ*(T:ℝ) := by
      rw [htarget,ENNReal.toReal_ofReal (mul_nonneg hκ.le T.coe_nonneg)]
    have hsg : stoppedGreen κ U γ G z u =
        ((2*z.im)*Real.exp (-u))^(-codimension κ)*
          (Real.sin (Complex.arg (G T z-(U T:ℂ))))^greenExponent κ := by
      change (if τ<∞ then greenDensity κ U γ G τ.toNNReal z else 0)=_
      rw [ite_eq_left hfin,hτT,ENNReal.toNNReal_coe,greenDensity,ite_eq_left hT,hTR]
    have hexp : 2*a κ*α κ*ℓ=(-u)*(-codimension κ) := by
      rw [alpha_eq κ hκ]
      dsimp only [a,u]
      field_simp [hκ.ne']
      ring
    have hinit : initialGreen κ z=(2*z.im)^(-codimension κ)*(Real.sin θ)^greenExponent κ := by
      rw [initialGreen]
      exact congrArg (fun s : ℝ => (2*z.im)^(-codimension κ)*s^greenExponent κ)
        (disk_center_sin_arg θ)
    rw [levelDensity,ite_eq_left htargetfin,htargreal,
      angle_eq_witness κ hκ b U γ G F hw hU θ 0 T hT,p_eq κ,hexp]
    change _=stoppedGreen κ U γ G z u/initialGreen κ z
    rw [hsg,hinit,Real.mul_rpow hc.le (Real.exp_pos _).le,← Real.exp_mul]
    field_simp [hA,hD]
    rfl
  · have htop : τ=∞ := top_le_iff.mp (not_lt.mp hfin)
    have htoptarget : levelTime κ θ b ℓ=∞ := by
      rw [htime,htop,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκ).ne']
    rw [levelDensity,htoptarget,ite_eq_right (not_lt_of_ge le_rfl)]
    change 0=(if τ<∞ then _ else 0)/_
    rw [ite_eq_right hfin,zero_div]

lemma levelDensity_eq_canonicalFiniteDensity
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (p : C(ℝ≥0,ℝ))
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → Real.sqrt κ*p s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ENNReal.ofReal (levelDensity κ θ b ℓ)=
      canonicalFiniteDensity κ (4*ℓ/κ,diskMapInv θ 0,p) := by
  rw [levelDensity_eq_stoppedGreen κ hκ b _ (p.continuous.const_mul _) γ G F hw hU θ hθ ℓ hℓ,
    canonicalFiniteDensity_eq κ p hw _ (div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le)]

theorem levelDensity_integrable_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ<8) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (b : Ω → Driver)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hU : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s →
      Real.sqrt κ*B s.toNNReal ω=driverValue (b ω) (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    Integrable (fun ω => levelDensity κ θ (b ω) ℓ) P ∧
      (∫ ω, levelDensity κ θ (b ω) ℓ ∂P)=1 := by
  let z := diskMapInv θ 0
  let u := 4*ℓ/κ
  have hz : z ∈ upperHalfPlane := diskMapInv_maps hθ (by simp)
  have hu : 0 ≤ u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hp : 0 < initialGreen κ z := initialGreen_pos κ z hz
  obtain ⟨hi,he⟩ := finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu
  have heq : (fun ω => stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) z u/initialGreen κ z) =ᵐ[P]
      (fun ω => levelDensity κ θ (b ω) ℓ) := by
    filter_upwards [hw,hU] with ω hω hmatch
    have heU : (fun t : ℝ≥0 => Real.sqrt κ*B t ω)=
        (fun t : ℝ≥0 => driverValue (b ω) (κ*(t:ℝ))) := by
      funext t
      simpa only [Real.toNNReal_coe] using hmatch t t.coe_nonneg
    have hc : Continuous (fun t : ℝ≥0 => Real.sqrt κ*B t ω) := by
      rw [heU]
      exact (b ω).continuous.comp (continuous_real_toNNReal.comp
        (continuous_const.mul continuous_subtype_val))
    exact (levelDensity_eq_stoppedGreen κ hκ (b ω) _ hc (γ ω)
      (G ω) (F ω) hω hmatch θ hθ ℓ hℓ).symm
  refine ⟨(hi.div_const _).congr heq,?_⟩
  rw [← integral_congr_ae heq,integral_div,he,div_self hp.ne']

end SLEExactGauge.Target

end

end OAI
