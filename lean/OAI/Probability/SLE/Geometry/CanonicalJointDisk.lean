import OAI.Probability.SLE.Mass.JointDiskMass
import OAI.Probability.SLE.Mass.CanonicalMassRemaining
import OAI.Probability.SLE.Geometry.CenteredDiskCoefficient

namespace OAI

/-! Joint angle and sample measurability of actual canonical disk masses
at radius stops. No angle-dependent exceptional set is selected. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma disk_at_parameter_measurable
    {Ξ : Type*} [MeasurableSpace Ξ] (θ : Ξ → ℝ) (hθ : Measurable θ)
    (g : Ξ → Ω) (hg : Measurable g) (T : Ξ → ℝ≥0∞) (hT : Measurable T) :
    Measurable (fun x => diskMassValue κ (θ x) (C.atTime (T x) (g x))) := by
  apply diskMassValue_measurable κ θ hθ
  · exact ((_root_.OAI.MeasureTheory.IsProgressive.parameter_time_measurable C.progressive g hg _ hT.ennreal_toNNReal).ite
      (measurableSet_lt hT measurable_const) (C.rational.terminal_measurable.comp hg))
  · intro x
    exact (C.atTime_radon (T x) (g x)).2

/-- The actual compact disk mass at the indicated logarithmic radius level.
Infinite radius times use the already constructed terminal measure. -/
def diskAtRadius (θ u : ℝ) (ω : Ω) : ℝ :=
  (diskMassValue κ θ (C.atTime
    (radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u) ω)).toReal

lemma diskAtRadius_nonneg (θ u : ℝ) (ω : Ω) : 0 ≤ C.diskAtRadius θ u ω :=
  ENNReal.toReal_nonneg

lemma diskAtRadius_joint_measurable
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) :
    Measurable (fun p : ℝ × Ω => C.diskAtRadius p.1 u p.2) := by
  have hz : Measurable (fun p : ℝ × Ω => Target.diskMapInv p.1 0) := by
    unfold Target.diskMapInv
    fun_prop
  have ht : Measurable (fun p : ℝ × Ω =>
      radiusLevelTime (γ p.2) (G p.2) (Target.diskMapInv p.1 0) u) := by
    have hj : Measurable (fun p : Ω × ℂ => radiusLevelTime (γ p.1) (G p.1) p.2 u) :=
      actual_radiusLevel_joint_measurable
        (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc κ u hu γ G F hw
    exact @Measurable.comp (ℝ × Ω) (Ω × ℂ) ℝ≥0∞
      inferInstance inferInstance inferInstance
      (fun p => radiusLevelTime (γ p.1) (G p.1) p.2 u)
      (fun p => (p.2,Target.diskMapInv p.1 0)) hj (measurable_snd.prodMk hz)
  exact (C.disk_at_parameter_measurable _ measurable_fst _ measurable_snd _ ht).ennreal_toReal

lemma diskAtRadius_eq_finite (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (u : ℝ) (σ : Ω → WithTop ℝ≥0) (ω : Ω)
    (he : σ ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u)
    (hf : σ ω≠⊤) :
    C.diskAtRadius θ u ω = finiteStoppedScalar (C.diskScalar θ hθ) σ ω := by
  rw [diskAtRadius,← he,diskMassValue_toReal_eq κ θ hθ]
  have hfin : (σ ω : ℝ≥0∞) < ∞ := lt_top_iff_ne_top.mpr hf
  simp only [atTime,extendedCanonicalMass,finiteStoppedScalar,hf,ite_false]
  split_ifs with hs
  · unfold diskScalar
    lift σ ω to ℝ≥0 using hf with t
    rfl
  · exact False.elim (hs hfin)

/-- The moment identity uses the same jointly measurable disk variable
which enters tail events, with exactly the prescribed inner-clock scaling. -/
lemma levelCoefficient_eq_diskAtRadius_moment [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    ENNReal.ofReal (Target.levelCoefficient κ W ℓ m θ) =
      ∫⁻ ω, ENNReal.ofReal (C.diskAtRadius θ (4*ℓ/κ) ω)^m
        ∂finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ) := by
  let u := 4*ℓ/κ
  have hu : 0 ≤ u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  let σ := fun ω => radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u
  have hz : Target.diskMapInv θ 0 ∈ upperHalfPlane := Target.diskMapInv_maps hθ (by simp)
  have hσ := actual_radiusLevelTime_stopping hB
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc h0
    κ hκ hκ8 γ G F hw (Target.diskMapInv θ 0) hz u hu
  have hf := finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F
    (Eventually.of_forall hw) (Target.diskMapInv θ 0) hz u u hu le_rfl σ
    (Eventually.of_forall (fun _ => le_rfl))
  rw [C.levelCoefficient_eq_centered_moment hB hc h0 hκ hκ8 F hw hgrowth W hW
    θ hθ ℓ hℓ m σ hσ (Eventually.of_forall (fun _ => rfl))]
  apply lintegral_congr_ae
  filter_upwards [hf] with ω hω
  rw [C.diskAtRadius_eq_finite θ hθ u σ ω rfl hω]

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
