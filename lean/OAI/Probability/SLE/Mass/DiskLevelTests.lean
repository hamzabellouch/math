import OAI.Probability.SLE.Gauge.DiskIntegratedMoments
import OAI.Probability.SLE.Mass.DiskLevelTransport
import OAI.Probability.SLE.Mass.CanonicalImageMass
import OAI.Probability.SLE.Mass.WeightedLevelMoments

namespace OAI

/-! Positive compact disk tests are dominated by physical level mass,
with the exact conformal derivative weight. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

lemma ofReal_disk_level_test_le
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (K : Set ℂ) (hK : IsCompact K) (hKd : K ⊆ ball 0 1)
    (f : C_c((ball (0:ℂ) 1),ℝ)) (hf : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1)
    (hfs : ∀ x : (ball (0:ℂ) 1), (x:ℂ)∉K → f x=0)
    (u : ℝ) (hu : 0≤u) (t : ℝ≥0∞) (ω : Ω) :
    ENNReal.ofReal (∫ x, f x ∂conformalMass (Target.diskHomeomorph θ hθ)
      (Target.diskMassWeight κ θ hθ) (halfPlaneLevelMeasure κ B γ G u t ω)) ≤
        diskLevelMass κ θ B γ G u K ω := by
  let g := conformalMassTest (Target.diskHomeomorph θ hθ) (Target.diskMassWeight κ θ hθ) f
  let S := Target.diskMapInv θ '' K
  have hS : IsCompact S := Target.diskCompactPreimage_compact θ hK hKd
  have hSH : S ⊆ upperHalfPlane := Target.diskCompactPreimage_subset hθ hKd
  have hg : ∀ z, 0≤g z := fun z => mul_nonneg (NNReal.coe_nonneg _) (hf _)
  have hgz (z : ℂ) (hz : z∉S) : extendHalfPlaneTest g z=0 := by
    by_cases hzH : z∈upperHalfPlane
    · rw [show z=(⟨z,hzH⟩:upperHalfPlane).val from rfl,extendHalfPlaneTest_apply]
      have hn : ((Target.diskHomeomorph θ hθ ⟨z,hzH⟩):ℂ)∉K := by
        intro h
        exact hz ⟨_,h,Target.diskMapInv_diskMap hθ hzH⟩
      change (Target.diskMassWeight κ θ hθ ⟨z,hzH⟩:ℝ)*
        f (Target.diskHomeomorph θ hθ ⟨z,hzH⟩)=0
      rw [hfs _ hn,mul_zero]
    · exact extendHalfPlaneTest_of_not_mem g z hzH
  rw [conformalMass_integral]
  change ENNReal.ofReal (∫ z, g z ∂halfPlaneLevelMeasure κ B γ G u t ω) ≤ _
  rw [ofReal_integral_halfPlaneLevelMeasure hκ hκ8 γ G F ω (hc ω) (hw ω) u t g hg]
  apply (levelApproximationTest_le_weightedLevelMass hm hc κ u hu γ G F hw S hS.measurableSet
    (fun z => ENNReal.ofReal (extendHalfPlaneTest g z))
    (extendHalfPlaneTest_measurable g g.continuous.measurable).ennreal_ofReal
    (fun z hz => by rw [hgz z hz,ENNReal.ofReal_zero]) t ω).trans
  calc
    weightedLevelMass κ B γ G u S (fun z => ENNReal.ofReal (extendHalfPlaneTest g z)) ω ≤
        ∫⁻ z in S, ENNReal.ofReal (‖deriv (Target.diskMap θ) z‖^dimension κ)*
          ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u) := by
      apply setLIntegral_mono' hS.measurableSet
      intro z hz
      apply mul_le_mul' ?_ le_rfl
      apply ENNReal.ofReal_le_ofReal
      rw [show z=(⟨z,hSH hz⟩:upperHalfPlane).val from rfl,extendHalfPlaneTest_apply]
      change (Target.diskMassWeight κ θ hθ ⟨z,hSH hz⟩:ℝ)*
        f (Target.diskHomeomorph θ hθ ⟨z,hSH hz⟩) ≤ _
      rw [Target.diskMassWeight_coe]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _) (hf1 _)
    _ = diskLevelMass κ θ B γ G u K ω := by
      rw [← Target.disk_level_integral_transport κ θ hθ K hK hKd]
      apply setLIntegral_congr_fun hK.measurableSet
      intro x hx
      exact (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm

end SLEExactGauge.Multipoint

end

end OAI
