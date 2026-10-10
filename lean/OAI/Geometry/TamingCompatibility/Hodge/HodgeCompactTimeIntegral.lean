import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixInitial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open MeasureTheory Set Filter
open scoped Topology
variable {V : Type*} [TopologicalSpace V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_integral_compact_positive (F F' : ℝ → V → ℝ)
    (K : Set V) (hK : IsCompact K)
    (hF : ∀ t, 0 < t → Continuous (F t))
    (hF' : ContinuousOn (fun p : ℝ × V => F' p.1 p.2) (Ioi 0 ×ˢ univ))
    (hsupp : ∀ t, 0 < t → Function.support (F t) ⊆ K)
    (hsupp' : ∀ t, 0 < t → Function.support (F' t) ⊆ K)
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t := by
  have hF'c (s : ℝ) (hs : 0 < s) : Continuous (F' s) :=
    continuousOn_univ.mp (hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hs,mem_univ _⟩))
  have hFc (s : ℝ) (hs : 0 < s) : HasCompactSupport (F s) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hsupp s hs) hK.isClosed)
  have hIc : IsCompact (Icc (t/2) (2*t) ×ˢ K) := isCompact_Icc.prod hK
  have hIsub : Icc (t/2) (2*t) ×ˢ K ⊆ Ioi 0 ×ˢ (univ : Set V) := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by linarith) hp.1.1,mem_univ _⟩
  obtain ⟨C,hC⟩ := hIc.exists_bound_of_continuousOn (hF'.mono hIsub)
  let b : V → ℝ := K.indicator (fun _ => max C 0)
  have hb : Integrable b μ :=
    (integrableOn_const (hK.measure_lt_top.ne)).integrable_indicator hK.isClosed.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := b) (s := Icc (t/2) (2*t))
    (Icc_mem_nhds (by linarith) (by linarith)) ?_
    ((hF t ht).integrable_of_hasCompactSupport (hFc t ht))
    (hF'c t ht).aestronglyMeasurable ?_ hb ?_).2
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hF s hs).aestronglyMeasurable
  · filter_upwards [] with x
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by linarith) hs.1
    by_cases hx : x ∈ K
    · exact (hC (s,x) ⟨hs,hx⟩).trans (by simp only [b,indicator_of_mem hx]; exact le_max_left _ _)
    · have hz : F' s x = 0 := by
        by_contra hn
        exact hx (hsupp' s hspos hn)
      simp [b,indicator_of_notMem hx,hz]
  · filter_upwards [] with x
    intro s hs
    exact hd s (lt_of_lt_of_le (by linarith) hs.1) x

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance compactTimeIntegralMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactTimeIntegralMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

lemma actual_cutoff_time_integral (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : Continuous η) (hc : HasCompactSupport η) :
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      (∫ z, normalDensity g B (q,z) * ⟪η z,
        deriv (fun s => normalGauge J α ht p D g B (q,z)
          (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t := by
  let G : Space → W →L[ℝ] W := fun z => normalGauge J α ht p D g B (q,z)
  let ρ : Space → ℝ := fun z => normalDensity g B (q,z)
  let k : ℝ → Space → W := fun s z => G z (χ z • NormalHeatResidual.modelSection s u z)
  let d : ℝ → Space → W := fun s z => G z (χ z • (((-2/s+‖z‖^2/(4*s^2))*FlatHeat.heat s z) • u))
  have hG : Continuous G := by
    have h : ContDiff ℝ ∞ G := by
      unfold G normalGauge
      exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
        (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
          (fun j => normalFirst J α ht p D g B j (q,0)))
    exact h.continuous
  have hρ : Continuous ρ := (normalDensity_continuous g B hg hB).comp
    (continuous_const.prodMk continuous_id)
  have hd (s : ℝ) (hs : 0 < s) (z : Space) : HasDerivAt (fun r => k r z) (d s z) s :=
    (G z).hasFDerivAt.comp_hasDerivAt s
      (((FlatHeat.heat_hasDerivAt_time hs z).smul_const u).const_smul (χ z))
  have hdc : ContinuousOn (fun v : ℝ × Space => d v.1 v.2) (Ioi 0 ×ˢ univ) := by
    intro v hv
    have hs : v.1 ≠ 0 := ne_of_gt hv.1
    have hh := (FlatHeat.heat_joint_contDiffAt (x := v) hs).continuousAt
    have hp : ContinuousAt (fun w : ℝ × Space => (-2/w.1+‖w.2‖^2/(4*w.1^2))*FlatHeat.heat w.1 w.2) v :=
      ((continuousAt_const.div continuousAt_fst hs).add
        ((continuousAt_snd.norm.pow 2).div (continuousAt_const.mul (continuousAt_fst.pow 2))
          (mul_ne_zero (by norm_num) (pow_ne_zero _ hs)))).mul hh
    exact ((hG.continuousAt.comp continuousAt_snd).clm_apply
      ((hχ.continuousAt.comp continuousAt_snd).smul (hp.smul continuousAt_const))).continuousWithinAt
  let F : ℝ → Space → ℝ := fun s z => ρ z * ⟪η z,k s z⟫
  let F' : ℝ → Space → ℝ := fun s z => ρ z * ⟪η z,d s z⟫
  have hi := hasDerivAt_integral_compact_positive volume F F' (tsupport η) hc
    (fun s _ => hρ.mul (hη.inner (hG.clm_apply (hχ.smul
      ((FlatHeat.heat_contDiff s).continuous.smul continuous_const)))))
    ((hρ.comp continuous_snd).continuousOn.mul ((hη.comp continuous_snd).continuousOn.inner hdc))
    (fun _ _ _ hz => by
      apply subset_tsupport η
      change η _ ≠ 0
      intro he
      exact hz (by simp [F,he]))
    (fun _ _ _ hz => by
      apply subset_tsupport η
      change η _ ≠ 0
      intro he
      exact hz (by simp [F',he]))
    (fun s hs z => by
      simpa only [inner_zero_left,add_zero] using
        ((hasDerivAt_const s (η z)).inner ℝ (hd s hs z)).const_mul (ρ z)) htpos
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact congrArg (fun w => ρ z * ⟪η z,w⟫) (hd t htpos z).deriv

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance compactTimeIntegralPatchMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactTimeIntegralPatchMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

lemma actual_cutoff_time_integral_local (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      (∫ z, normalDensity g B (q,z) * ⟪η z,
        deriv (fun s => normalGauge J α ht p D g B (q,z)
          (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t := by
  obtain ⟨η',hη',hc,_,he⟩ := exists_compact_smooth_extension hU hχc hχU hη
  have hi := actual_cutoff_time_integral J α ht p D g B hg hB q χ hχ htpos u η' hη'.continuous hc
  have hpair (s : ℝ) (z : Space) :
      ⟪η' z,normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫ =
      ⟪η z,normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫ := by
    by_cases hz : z ∈ tsupport χ
    · rw [(he z hz).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hd (z : Space) :
      ⟪η' z,deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t⟫ =
      ⟪η z,deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t⟫ := by
    by_cases hz : z ∈ tsupport χ
    · rw [(he z hz).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  simpa only [hpair,hd] using hi

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
