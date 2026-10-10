import Mathlib
import OAI.Probability.SLE.TraceMeasurability

namespace OAI

/-! Sausage Charge for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance wholeSausageChargePathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance wholeSausageChargePathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

 
def wholeSausageSet (γ : ℝ≥0 → ℂ) (v : ℝ) : Set ℂ :=
  {z | ∃ t : ℝ≥0, dist (γ t) z < v}

 
def wholeSausageCharge (κ : ℝ) (γ : ℝ≥0 → ℂ) (v : ℝ) (A : Set ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (v ^ (-codimension κ)) * volume (A ∩ wholeSausageSet γ v)

lemma wholeSausageSet_isOpen (γ : ℝ≥0 → ℂ) (v : ℝ) :
    IsOpen (wholeSausageSet γ v) := by
  have he : wholeSausageSet γ v = ⋃ t : ℝ≥0, ball (γ t) v := by
    ext z
    simp [wholeSausageSet, dist_comm]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_ball

lemma wholeSausage_joint_open (v : ℝ) :
    IsOpen {p : C(ℝ≥0, ℂ) × ℂ | p.2 ∈ wholeSausageSet p.1 v} := by
  have he : {p : C(ℝ≥0, ℂ) × ℂ | p.2 ∈ wholeSausageSet p.1 v} =
      ⋃ t : ℝ≥0, {p : C(ℝ≥0, ℂ) × ℂ | dist (p.1 t) p.2 < v} := by
    ext p
    simp [wholeSausageSet]
  rw [he]
  exact isOpen_iUnion fun t => isOpen_lt
    (((continuous_eval_const t).comp continuous_fst).dist continuous_snd) continuous_const

lemma wholeSausageCharge_measurable (κ v : ℝ) (A : Set ℂ) :
    Measurable (fun g : C(ℝ≥0, ℂ) => wholeSausageCharge κ g v A) := by
  classical
  have hm : Measurable (fun p : C(ℝ≥0, ℂ) × ℂ =>
      if p.2 ∈ wholeSausageSet p.1 v then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (wholeSausage_joint_open v).measurableSet measurable_const measurable_const
  apply measurable_const.mul
  have hh := hm.lintegral_prod_right' (ν := volume.restrict A)
  convert hh using 1
  ext g
  change volume (A ∩ wholeSausageSet g v) =
    ∫⁻ z, (wholeSausageSet g v).indicator (fun _ => 1) z ∂(volume.restrict A)
  rw [lintegral_indicator (wholeSausageSet_isOpen g v).measurableSet]
  simp [Measure.restrict_apply (wholeSausageSet_isOpen g v).measurableSet, inter_comm]

 
lemma wholeSausageCharge_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f) (κ v : ℝ) (A : Set ℂ) :
    (∫⁻ ω, wholeSausageCharge κ (f ω) v A ∂P) =
      ∫⁻ z in A, ENNReal.ofReal (v ^ (-codimension κ)) *
        P {ω | ∃ t : ℝ≥0, dist (f ω t) z < v} := by
  classical
  let I : Ω × ℂ → ℝ≥0∞ := fun p =>
    if p.2 ∈ wholeSausageSet (f p.1) v then 1 else 0
  have hset : MeasurableSet {p : Ω × ℂ | p.2 ∈ wholeSausageSet (f p.1) v} :=
    (wholeSausage_joint_open v).measurableSet.preimage
      ((hf.comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable I := Measurable.ite hset measurable_const measurable_const
  have hre (ω : Ω) : wholeSausageCharge κ (f ω) v A =
      ENNReal.ofReal (v ^ (-codimension κ)) *
        ∫⁻ z, I (ω, z) ∂(volume.restrict A) := by
    unfold wholeSausageCharge
    congr 1
    change volume (A ∩ wholeSausageSet (f ω) v) =
      ∫⁻ z, (wholeSausageSet (f ω) v).indicator (fun _ => 1) z ∂(volume.restrict A)
    rw [lintegral_indicator (wholeSausageSet_isOpen (f ω) v).measurableSet]
    simp [Measure.restrict_apply (wholeSausageSet_isOpen (f ω) v).measurableSet, inter_comm]
  have hem (z : ℂ) : MeasurableSet {ω | ∃ t : ℝ≥0, dist (f ω t) z < v} :=
    hset.preimage (measurable_id.prodMk measurable_const)
  have hei (z : ℂ) : (∫⁻ ω, I (ω, z) ∂P) =
      P {ω | ∃ t : ℝ≥0, dist (f ω t) z < v} := by
    exact lintegral_indicator_one (hem z)
  simp_rw [hre]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hI.aemeasurable]
  simp_rw [hei]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

 
def wholeSausageChargeBound (κ R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in closedBall (0 : ℂ) R,
    ENNReal.ofReal (sausagePointConstant κ * |z.im| ^ (-codimension κ))

lemma wholeSausageChargeBound_lt_top (κ R : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    wholeSausageChargeBound κ R < ∞ := by
  have hi : Integrable (fun z : ℂ =>
      sausagePointConstant κ * |z.im| ^ (-codimension κ))
      (volume.restrict (closedBall (0 : ℂ) R)) :=
    (integrable_height_power_ball (codimension κ) R (codimension_lt_one κ hκ)).const_mul _
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun (z : ℂ) =>
    mul_nonneg (sausagePointConstant_pos κ hκ hκ8).le
      (Real.rpow_nonneg (abs_nonneg z.im) _))).mp hi.2

lemma regularSLE_wholeSausageCharge_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hc : ∀ ω, Continuous (γ ω)) (R v : ℝ) (hv : 0 < v) :
    (∫⁻ ω, wholeSausageCharge κ (γ ω) v (closedBall 0 R) ∂P) ≤
      wholeSausageChargeBound κ R := by
  let f : Ω → C(ℝ≥0, ℂ) := fun ω => ⟨γ ω, hc ω⟩
  have hf : Measurable f := source_whole_path_measurable f hSLE.1
  change (∫⁻ ω, wholeSausageCharge κ (f ω) v (closedBall 0 R) ∂P) ≤ _
  rw [wholeSausageCharge_expectation P f hf]
  obtain ⟨B, G, F, hB, hw⟩ := hSLE.exists_charts
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae ae_im_ne_zero] with z hz
  have hb := normalized_visit_bound hB κ hκ hκ8 γ G F hw z hz v hv
  have he : P {ω | ∃ t : ℝ≥0, dist (f ω t) z < v} =
      ENNReal.ofReal (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < v}).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
  rw [he, ← ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _)]
  exact ENNReal.ofReal_le_ofReal hb

 

theorem source_cover_charge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P) (R : ℝ) :
    wholeSausageChargeBound κ R < ∞ ∧
    ∀ v : ℝ, 0 < v →
      AEMeasurable (fun ω => wholeSausageCharge κ (γ ω) v (closedBall 0 R)) P ∧
      (∫⁻ ω, wholeSausageCharge κ (γ ω) v (closedBall 0 R) ∂P) ≤
        wholeSausageChargeBound κ R := by
  classical
  refine ⟨wholeSausageChargeBound_lt_top κ R hκ hκ8, ?_⟩
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  let Q := P.comap (Subtype.val : a.samples → Ω)
  have : IsProbabilityMeasure Q := a.probability
  let g : a.samples → ℝ≥0 → ℂ := fun ω => γ ω
  have hsle : IsOrdinaryChordalSLE κ g Q := by
    refine ⟨fun t => (hSLE.1 t).comp measurable_subtype_coe, a.B, a.brownian, ?_⟩
    exact Eventually.of_forall fun ω => ⟨a.G ω, a.F ω, a.witness ω⟩
  let f : a.samples → C(ℝ≥0, ℂ) := fun ω => ⟨g ω, a.trace_continuous ω⟩
  have hfm : Measurable f := source_whole_path_measurable f hsle.1
  intro v hv
  have hm := (wholeSausageCharge_measurable κ v (closedBall (0 : ℂ) R)).comp hfm
  change Measurable (fun ω : a.samples => wholeSausageCharge κ (g ω) v (closedBall 0 R)) at hm
  have hb := regularSLE_wholeSausageCharge_bound Q κ hκ hκ8 g hsle a.trace_continuous R v hv
  have hemb : MeasurableEmbedding (Subtype.val : a.samples → Ω) :=
    MeasurableEmbedding.subtype_coe a.measurable_samples
  constructor
  · exact (a.measurePreserving_val.aemeasurable_comp_iff hemb).mp hm.aemeasurable
  · have he := a.measurePreserving_val.lintegral_comp_emb hemb
      (fun ω => wholeSausageCharge κ (γ ω) v (closedBall 0 R))
    change (∫⁻ ω, wholeSausageCharge κ (g ω) v (closedBall 0 R) ∂Q) = _ at he
    rw [← he]
    exact hb

 

lemma source_cover_charge_sup
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (R : ℝ) (_hR : 0 < R) :
    ∃ C : ℝ≥0, (⨆ (v : ℝ) (_ : 0 < v) (_ : v ≤ 1),
      ∫⁻ ω, wholeSausageCharge κ (γ ω) v (ball 0 R) ∂P) ≤ C := by
  obtain ⟨hfinite, hbound⟩ := source_cover_charge P κ hκ hκ8 γ hSLE R
  refine ⟨(wholeSausageChargeBound κ R).toNNReal, ?_⟩
  rw [ENNReal.coe_toNNReal hfinite.ne]
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun _hv1 => ?_
  apply le_trans _ (hbound v hv).2
  apply lintegral_mono
  intro ω
  apply mul_le_mul' le_rfl
  exact measure_mono (inter_subset_inter_left _ ball_subset_closedBall)
end
end SLEExactGauge
end

 

end
end
end

end OAI
