import Mathlib
import OAI.MathematicalPhysics.BFSS.NormalTubes
import OAI.MathematicalPhysics.BFSS.NormalCharts

namespace OAI

/-! Slice densities and compact gauge Haar measures. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

def normalPatchDensity (q : Boson N) (U : Set (Boson N)) (b : Boson N → ℝ)
    (v : M.SliceParameter q) : ℝ :=
  U.indicator (fun x => |M.normalChartJacobian q x| * b (M.normalEuclideanChart q x))
    (M.sliceLinearEquiv q v)

def normalSliceDensity (q : Boson N) (U : Set (Boson N)) (b : Boson N → ℝ)
    (z : M.normalSlice q) : ℝ :=
  ∫ t : LinearMap.range (M.gaugeTangent q), M.normalPatchDensity q U b (t,z)

lemma normalEuclideanChart_sliceLinearEquiv (q : Boson N) (v : M.SliceParameter q) :
    M.normalEuclideanChart q (M.sliceLinearEquiv q v) = M.normalChartMap q v := by
  simp only [normalEuclideanChart,ContinuousLinearEquiv.symm_apply_apply]

theorem normalPatch_integral (q : Boson N) (U : Set (Boson N))
    (hU : MeasurableSet U) (hUi : InjOn (M.normalEuclideanChart q) U)
    (b F : Boson N → ℝ)
    (hb : Function.support b ⊆ M.normalEuclideanChart q '' U)
    (hF : ∀ V : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction V x) = F x) :
    (∫ x, b x * F x) = ∫ v : M.SliceParameter q,
      M.normalPatchDensity q U b v * F (q+(v.2 : Boson N)) := by
  have hder (x : Boson N) (_hx : x ∈ U) :=
    ((M.normalEuclideanChart_contDiff q).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt (s := U)
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hU hder hUi
    (fun x => b x * F x)
  have hout : (∫ x in M.normalEuclideanChart q '' U, b x * F x) = ∫ x, b x * F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : b x = 0 := by simpa only [Function.mem_support,not_not] using mt (hb (a := x)) hx
      rw [hz,zero_mul])
  rw [hout] at hi
  rw [hi,←integral_indicator hU]
  have he := (M.sliceLinearEquiv_measurePreserving q).integral_comp
    (M.sliceLinearEquiv q).toHomeomorph.measurableEmbedding
    (U.indicator (fun x => |M.normalChartJacobian q x| * (b (M.normalEuclideanChart q x) * F (M.normalEuclideanChart q x))))
  change _ = _ at he
  change (∫ x, U.indicator (fun x => |M.normalChartJacobian q x| *
    (b (M.normalEuclideanChart q x) * F (M.normalEuclideanChart q x))) x) = _
  rw [←he]
  apply integral_congr_ae
  filter_upwards with v
  unfold normalPatchDensity
  by_cases hv : M.sliceLinearEquiv q v ∈ U
  · rw [Set.indicator_of_mem hv,Set.indicator_of_mem hv,M.normalEuclideanChart_sliceLinearEquiv,
      M.normalChartMap_invariant q F hF]
    ring
  · rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem hv,zero_mul]

lemma normalPatch_integrable (q : Boson N) (U : Set (Boson N))
    (hU : MeasurableSet U) (hUi : InjOn (M.normalEuclideanChart q) U)
    (b F : Boson N → ℝ) (hb : Continuous b) (hFc : Continuous F)
    (hFK : HasCompactSupport F)
    (hF : ∀ V : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction V x) = F x) :
    Integrable (fun v : M.SliceParameter q =>
      M.normalPatchDensity q U b v * F (q+(v.2 : Boson N))) volume := by
  have hder (x : Boson N) (_hx : x ∈ U) :=
    ((M.normalEuclideanChart_contDiff q).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt (s := U)
  have hbi : Integrable (fun x => b x * F x) volume :=
    (hb.mul hFc).integrable_of_hasCompactSupport hFK.mul_left
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hder hUi
    (fun x => b x * F x)).mp hbi.integrableOn
  have hi' := (integrable_indicator_iff hU).mpr hi
  have hp := ((M.sliceLinearEquiv_measurePreserving q).integrable_comp
    hi'.aestronglyMeasurable).mpr hi'
  convert hp using 1
  funext v
  change M.normalPatchDensity q U b v * F (q+(v.2 : Boson N)) =
    U.indicator (fun x => |M.normalChartJacobian q x| *
      (b (M.normalEuclideanChart q x) * F (M.normalEuclideanChart q x))) (M.sliceLinearEquiv q v)
  unfold normalPatchDensity
  by_cases hv : M.sliceLinearEquiv q v ∈ U
  · rw [Set.indicator_of_mem hv,Set.indicator_of_mem hv,M.normalEuclideanChart_sliceLinearEquiv,
      M.normalChartMap_invariant q F hF]
    ring
  · rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem hv,zero_mul]

theorem normalSlice_integral (q : Boson N) (U : Set (Boson N))
    (hU : MeasurableSet U) (hUi : InjOn (M.normalEuclideanChart q) U)
    (b F : Boson N → ℝ) (hb : Continuous b) (hFc : Continuous F)
    (hFK : HasCompactSupport F)
    (hsupp : Function.support b ⊆ M.normalEuclideanChart q '' U)
    (hF : ∀ V : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction V x) = F x) :
    (∫ x, b x * F x) = ∫ z : M.normalSlice q,
      M.normalSliceDensity q U b z * F (q+(z : Boson N)) := by
  rw [M.normalPatch_integral q U hU hUi b F hsupp hF]
  have hi := M.normalPatch_integrable q U hU hUi b F hb hFc hFK hF
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards with z
  exact integral_mul_const _ _

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

local instance gaugeMeasurableSpace : MeasurableSpace (unitary (ColorMatrix N)) := borel _
local instance gaugeBorelSpace : BorelSpace (unitary (ColorMatrix N)) := ⟨rfl⟩

def gaugeIsometry (U : unitary (ColorMatrix N)) : Boson N ≃ₗᵢ[ℝ] Boson N where
  toFun := M.gaugeAction U
  invFun := M.gaugeAction U⁻¹
  left_inv := M.gaugeAction_inv U
  right_inv x := by
    simpa only [inv_inv] using M.gaugeAction_inv U⁻¹ x
  map_add' := M.gaugeAction_add U
  map_smul' := M.gaugeAction_smul U
  norm_map' := M.gaugeAction_norm U

lemma gaugeAction_measurePreserving (U : unitary (ColorMatrix N)) :
    MeasurePreserving (M.gaugeAction U) volume volume :=
  (M.gaugeIsometry U).measurePreserving

lemma gaugeAction_continuous :
    Continuous (fun p : unitary (ColorMatrix N) × Boson N => M.gaugeAction p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  change Continuous (fun z : unitary (ColorMatrix N) × Boson N =>
    M.colorExtract ((z.1 : ColorMatrix N)*M.colorEmbed (spatialColor z.2 p.1)*
      (z.1 : ColorMatrix N)ᴴ) p.2)
  exact (PiLp.continuous_apply 2 _ p.2).comp
    (M.colorExtract.toContinuousLinearMap.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).mul
        (M.colorEmbed.toContinuousLinearMap.continuous.comp
          ((spatialColorMap (N := N) p.1).toContinuousLinearMap.continuous.comp continuous_snd))).mul
        (continuous_subtype_val.comp continuous_fst).star))

lemma gaugeAction_image_zeros (U : unitary (ColorMatrix N)) :
    M.gaugeAction U '' M.massiveZeros = M.massiveZeros := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact M.gaugeConjugate_mem_massiveZeros U U.prop x hx
  · intro x hx
    refine ⟨M.gaugeAction U⁻¹ x,M.gaugeConjugate_mem_massiveZeros ((U⁻¹ : unitary (ColorMatrix N)) : ColorMatrix N) (U⁻¹).prop x hx,?_⟩
    simpa only [inv_inv] using M.gaugeAction_inv U⁻¹ x

lemma gaugeAction_infDist (U : unitary (ColorMatrix N)) (x : Boson N) :
    Metric.infDist (M.gaugeAction U x) M.massiveZeros = Metric.infDist x M.massiveZeros := by
  have hd := Metric.infDist_image (t := M.massiveZeros) (x := x) (M.gaugeIsometry U).isometry
  change Metric.infDist (M.gaugeAction U x) (M.gaugeAction U '' M.massiveZeros) = _ at hd
  rwa [M.gaugeAction_image_zeros] at hd

def gaugePositiveCompact (hN : 2 ≤ N) : PositiveCompacts (unitary (ColorMatrix N)) where
  carrier := Set.univ
  isCompact' := by
    let : CompactSpace (unitary (ColorMatrix N)) :=
      isCompact_iff_compactSpace.mp (BFSSOrbit.unitary_compact hN)
    exact isCompact_univ
  interior_nonempty' := by simp

def gaugeHaar (hN : 2 ≤ N) : Measure (unitary (ColorMatrix N)) :=
  Measure.haarMeasure (gaugePositiveCompact hN)

instance gaugeHaar_isHaar (hN : 2 ≤ N) : (gaugeHaar hN).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance gaugeHaar_isProbability (hN : 2 ≤ N) : IsProbabilityMeasure (gaugeHaar hN) where
  measure_univ := by
    change Measure.haarMeasure (gaugePositiveCompact hN) (gaugePositiveCompact hN) = 1
    exact Measure.haarMeasure_self

def gaugeOrbitMeasure (hN : 2 ≤ N) (q : Boson N) : Measure (Boson N) :=
  Measure.map (fun U => M.gaugeAction U q) (gaugeHaar hN)

lemma gaugeOrbitMap_continuous (q : Boson N) :
    Continuous (fun U : unitary (ColorMatrix N) => M.gaugeAction U q) := by
  have hc : Continuous (fun U : unitary (ColorMatrix N) => (U,q)) :=
    continuous_id.prodMk continuous_const
  have hh := M.gaugeAction_continuous.comp hc
  exact hh

instance gaugeOrbitMeasure_isProbability (hN : 2 ≤ N) (q : Boson N) :
    IsProbabilityMeasure (M.gaugeOrbitMeasure hN q) := by
  unfold gaugeOrbitMeasure
  infer_instance

lemma gauge_average_on_orbit (hN : 2 ≤ N) (f : Boson N → ℝ) (q : Boson N)
    (U : unitary (ColorMatrix N)) :
    (∫ V, f (M.gaugeAction V⁻¹ (M.gaugeAction U q)) ∂gaugeHaar hN) =
      ∫ V, f (M.gaugeAction V⁻¹ q) ∂gaugeHaar hN := by
  have he := integral_mul_left_eq_self (μ := gaugeHaar hN)
    (fun V => f (M.gaugeAction V⁻¹ q)) U⁻¹
  simp only [_root_.mul_inv_rev,inv_inv,M.gaugeAction_mul] at he
  exact he

end
end BFSSQuantum.AlgebraData

end OAI
