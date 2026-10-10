import OAI.Probability.SLE.Geometry.DiskQuarterDistortion
import OAI.Probability.SLE.Angle.TargetDiskMass
import OAI.Probability.SLE.Mass.CompactImageMassBounds

namespace OAI

/-! Exact disk-coordinate pushforward mass and its two-sided comparison.
The disk scalar is the same weighted canonical scalar used in the prescribed
moment coefficients. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint

lemma Target.mem_diskSourceHalfPlane_iff {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (z : upperHalfPlane) :
    z ∈ Target.diskSourceHalfPlane θ ↔ Target.diskMap θ z ∈ Target.diskK := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hh := congrArg (Target.diskMap θ) he
    rw [Target.diskMap_diskMapInv hθ (Target.diskK_subset_unit hw)] at hh
    rwa [← hh]
  · intro hz
    exact ⟨Target.diskMap θ z,hz,Target.diskMapInv_diskMap hθ z.property⟩

lemma Multipoint.ofReal_compactWeightedMass
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    ENNReal.ofReal (compactWeightedMass w K μ) = ∫⁻ z in K, (w z:ℝ≥0∞) ∂μ := by
  have hh := ofReal_integral_eq_lintegral_ofReal (compact_weight_integrable w K hK μ)
    (ae_of_all _ (fun z => (w z).coe_nonneg))
  simpa only [compactWeightedMass,ENNReal.ofReal_coe_nnreal] using hh

def diskChartMass (κ θ : ℝ) (f : ℂ → ℂ) (μ : Measure upperHalfPlane) : Measure ℂ :=
  weightedImageMass (fun z : upperHalfPlane => f (Target.diskMap θ z))
    (fun z : upperHalfPlane => ENNReal.ofReal
      (‖deriv (f ∘ Target.diskMap θ) z‖^dimension κ)) μ

lemma diskChartMass_quarter_bounds (hgrowth : PublishedDiskUnivalentGrowth)
    (κ : ℝ) (hκ : 0 < κ) (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    ENNReal.ofReal ((‖deriv f 0‖/16)^dimension κ) *
        ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
          (Target.diskSourceHalfPlane θ) μ) ≤ diskChartMass κ θ f μ (f '' Target.diskK) ∧
    diskChartMass κ θ f μ (f '' Target.diskK) ≤
      ENNReal.ofReal ((16*‖deriv f 0‖)^dimension κ) *
        ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
          (Target.diskSourceHalfPlane θ) μ) := by
  let K := Target.diskSourceHalfPlane θ
  let J := fun z : upperHalfPlane => f (Target.diskMap θ z)
  let v := fun z : upperHalfPlane => (Target.diskMassWeight κ θ hθ z:ℝ≥0∞)
  let w := fun z : upperHalfPlane => ENNReal.ofReal (‖deriv (f ∘ Target.diskMap θ) z‖^dimension κ)
  have hK : IsCompact K := Target.diskSourceHalfPlane_compact hθ
  have hmap := Target.diskMap_maps hθ
  have hJ : Measurable J :=
    (hd.continuousOn.comp_continuous
      ((Target.diskHomeomorph θ hθ).continuous_toFun.subtype_val)
      (fun z => hmap z.property)).measurable
  have himage : IsCompact (f '' Target.diskK) :=
    (isCompact_closedBall (0:ℂ) (1/4)).image_of_continuousOn
      (hd.continuousOn.mono Target.diskK_subset_unit)
  have hpre : J ⁻¹' (f '' Target.diskK)=K := by
    ext z
    rw [Target.mem_diskSourceHalfPlane_iff hθ]
    constructor
    · rintro ⟨x,hx,hxe⟩
      have he : x=Target.diskMap θ z := hi (Target.diskK_subset_unit hx) (hmap z.property) hxe
      rwa [← he]
    · intro hz
      exact ⟨Target.diskMap θ z,hz,rfl⟩
  have he : diskChartMass κ θ f μ (f '' Target.diskK) = ∫⁻ z in K, w z ∂μ := by
    change weightedImageMass J w μ _ = _
    rw [weightedImageMass,Measure.map_apply hJ himage.measurableSet,hpre,withDensity_apply _ hK.measurableSet]
  have hw (z : upperHalfPlane) : w z =
      ENNReal.ofReal (‖deriv f (Target.diskMap θ z)‖^dimension κ)*v z := by
    dsimp only [w,v]
    rw [Target.diskMassWeight_ennreal]
    symm
    rw [mul_comm]
    exact derivative_dimension_weight_comp κ f (Target.diskMap θ) z
      (hd.differentiableAt (isOpen_ball.mem_nhds (hmap z.property)))
      (Target.diskMap_hasDerivAt hθ z.property).differentiableAt
  have hd0 : 0 ≤ dimension κ := by unfold dimension; linarith
  have hbounds (z : upperHalfPlane) (hz : z∈K) :
      ENNReal.ofReal ((‖deriv f 0‖/16)^dimension κ)*v z ≤ w z ∧
      w z ≤ ENNReal.ofReal ((16*‖deriv f 0‖)^dimension κ)*v z := by
    have hz' : Target.diskMap θ z ∈ Target.diskK := (Target.mem_diskSourceHalfPlane_iff hθ z).mp hz
    have hn : ‖Target.diskMap θ z‖ ≤ 1/4 := by
      simpa only [Target.diskK,mem_closedBall,dist_zero_right] using hz'
    have hb := univalent_quarter_derivative_bounds hgrowth hd hi hn
    rw [hw]
    constructor
    · apply mul_le_mul' _ le_rfl
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hb.1 hd0)
    · apply mul_le_mul' _ le_rfl
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hb.2 hd0)
  rw [ofReal_compactWeightedMass _ _ hK μ,he]
  change ENNReal.ofReal ((‖deriv f 0‖/16)^dimension κ)*(∫⁻ z in K, v z ∂μ) ≤ _ ∧
    _ ≤ ENNReal.ofReal ((16*‖deriv f 0‖)^dimension κ)*(∫⁻ z in K, v z ∂μ)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ⟨setLIntegral_mono' hK.measurableSet (fun z hz => (hbounds z hz).1),
    setLIntegral_mono' hK.measurableSet (fun z hz => (hbounds z hz).2)⟩

end SLEExactGauge

end

end OAI
