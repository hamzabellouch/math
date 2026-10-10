import Mathlib
import OAI.Probability.SLE.SausageSeedAll

namespace OAI

/-! Trace Measurability for chordal SLE. -/

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
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance wholeTraceMeasurabilityPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance wholeTraceMeasurabilityPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_whole_trace_measure_measurable (h : ℝ → ℝ) (hh : IsGauge h)
    (C : Set ℂ) (hC : IsClosed C) :
    Measurable (fun γ : C(ℝ≥0,ℂ) => hausdorffGauge h (range γ ∩ C)) := by
  have heq : (fun γ : C(ℝ≥0,ℂ) => hausdorffGauge h (range γ ∩ C)) =
      fun γ : C(ℝ≥0,ℂ) => ⨆ n : ℕ, hausdorffGauge h (C ∩ (γ '' Icc 0 (n : ℝ≥0))) := by
    funext γ
    have hU : range γ ∩ C = ⋃ n : ℕ, C ∩ (γ '' Icc 0 (n : ℝ≥0)) := by
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,hc⟩
        obtain ⟨n,hn⟩ := exists_nat_ge t
        exact mem_iUnion.mpr ⟨n,hc,t,⟨zero_le,hn⟩,rfl⟩
      · intro hz
        obtain ⟨n,hc,t,ht,rfl⟩ := mem_iUnion.mp hz
        exact ⟨mem_range_self t,hc⟩
    rw [hU]
    apply Monotone.measure_iUnion
    intro i j hij
    exact inter_subset_inter_right C (image_mono (Icc_subset_Icc_right (Nat.cast_le.mpr hij)))
  rw [heq]
  exact Measurable.iSup (fun n => source_compact_trace_measure_measurable h hh C hC 0 n)

lemma source_whole_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0,ℂ)) (hf : ∀ t, Measurable (fun ω => f ω t)) : Measurable f := by
  have he : MeasurableEmbedding (fun g : C(ℝ≥0,ℂ) => fun n => g (denseSeq ℝ≥0 n)) := by
    apply Continuous.measurableEmbedding
    · exact continuous_pi fun n => continuous_eval_const _
    · intro g₁ g₂ h
      apply DFunLike.coe_injective
      exact (denseRange_denseSeq ℝ≥0).equalizer g₁.continuous g₂.continuous h
  apply he.measurable_comp_iff.mp
  exact Measurable.of_eval (fun index => hf (denseSeq ℝ≥0 index))

lemma source_sle_whole_trace_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) (h : ℝ → ℝ) (hh : IsGauge h)
    (C : Set ℂ) (hC : IsClosed C) :
    AEMeasurable (fun ω => hausdorffGauge h (wholeTrace (γ ω) ∩ C)) P := by
  classical
  have hcont : ∀ᵐ ω ∂P, Continuous (γ ω) := by
    obtain ⟨B,hB,hcap⟩ := hSLE.2
    filter_upwards [hcap] with ω hω
    obtain ⟨G,F,hGF⟩ := hω
    exact hGF.1
  obtain ⟨S,hS,hSm,hSc⟩ := hcont.exists_measurable_mem
  let f : Ω → C(ℝ≥0,ℂ) := fun ω => if hω : ω ∈ S then ⟨γ ω,hSc ω hω⟩ else 0
  have hfm : Measurable f := by
    apply source_whole_path_measurable
    intro t
    have hm : Measurable (fun ω => if ω ∈ S then γ ω t else (0 : ℂ)) :=
      Measurable.ite hSm (hSLE.1 t) measurable_const
    convert hm using 1
    funext ω
    by_cases hω : ω ∈ S <;> simp [f,hω]
  apply ((source_whole_trace_measure_measurable h hh C hC).comp hfm).aemeasurable.congr
  filter_upwards [hS] with ω hω
  simp [f,hω,wholeTrace]
end
end SLEExactGauge

namespace SLEExactGauge
universe v_meas
 
def SourceWholeTraceMeasurableTarget : Prop :=
  ∀ (Ω : Type v_meas) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∀ R : ℝ, 0 < R → AEMeasurable (fun ω => hausdorffGauge h
    (wholeTrace (γ ω) ∩ Metric.closedBall 0 R)) P
end SLEExactGauge
namespace SLEExactGauge
theorem sourceWholeTraceMeasurable_proved : SourceWholeTraceMeasurableTarget := by
  intro Ω m P hP κ hκ hκ8 γ hSLE h hh hf R hR
  exact source_sle_whole_trace_aemeasurable P κ γ hSLE h hh _ isClosed_closedBall
end SLEExactGauge
end

 

end
end
end

end OAI
