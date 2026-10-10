import Mathlib
import OAI.Probability.SLE.TraceMeasurability

namespace OAI

/-! Main Reduction for chordal SLE. -/

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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

 

def FiniteExpectedWholeTrace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → (∫⁻ ω, hausdorffGauge h
    (wholeTrace (γ ω) ∩ Metric.closedBall 0 R) ∂P) < ∞

lemma integerRectangle_subset_closedBall (m : ℕ) :
    integerRectangle m ⊆ Metric.closedBall (0 : ℂ) (2 * (m : ℝ)) := by
  intro z hz
  have hre : |z.re| ≤ (m : ℝ) := abs_le.mpr ⟨hz.1, hz.2.1⟩
  have him : |z.im| ≤ (m : ℝ) := by
    rw [abs_of_nonneg hz.2.2.1]
    exact hz.2.2.2
  have hn : ‖z‖ ≤ 2 * (m : ℝ) :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

 

lemma trace_inter_bounded_lt_top_of_integer_balls
    (h : ℝ → ℝ) (γ : ℝ≥0 → ℂ)
    (hballs : ∀ n : ℕ, hausdorffGauge h
      (wholeTrace γ ∩ Metric.closedBall 0 ((n : ℝ) + 1)) < ∞)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    hausdorffGauge h (wholeTrace γ ∩ K) < ∞ := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : K ⊆ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (by linarith))
  exact (measure_mono (inter_subset_inter_right _ hsub)).trans_lt (hballs n)

 

lemma segment_lt_top_of_integer_balls
    (h : ℝ → ℝ) (γ : ℝ≥0 → ℂ) (hc : Continuous γ)
    (hballs : ∀ n : ℕ, hausdorffGauge h
      (wholeTrace γ ∩ Metric.closedBall 0 ((n : ℝ) + 1)) < ∞)
    (s t : ℝ≥0) : hausdorffGauge h (segment γ s t) < ∞ := by
  have hK : Bornology.IsBounded (segment γ s t) :=
    (isCompact_Icc.image hc).isBounded
  have hf := trace_inter_bounded_lt_top_of_integer_balls h γ hballs _ hK
  have hsub : segment γ s t ⊆ wholeTrace γ := image_subset_range _ _
  simpa only [inter_eq_right.mpr hsub] using hf

 

lemma mainEvent_of_integer_balls {Ω : Type*}
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) (ω : Ω)
    (hc : Continuous (γ ω))
    (hlo : ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (segment (γ ω) s t))
    (hballs : ∀ n : ℕ, hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 ((n : ℝ) + 1)) < ∞) :
    ω ∈ MainEvent h γ := by
  constructor
  · intro s t hs hst
    exact ⟨hlo s t hs hst, segment_lt_top_of_integer_balls h (γ ω) hc hballs s t⟩
  · intro m _hm
    apply trace_inter_bounded_lt_top_of_integer_balls h (γ ω) hballs
    exact Metric.isBounded_closedBall.subset (integerRectangle_subset_closedBall m)

 

lemma ae_integer_balls_lt_top_of_finiteExpectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hm : ∀ R : ℝ, 0 < R → AEMeasurable (fun ω => hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 R)) P)
    (he : FiniteExpectedWholeTrace P h γ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 ((n : ℝ) + 1)) < ∞ := by
  apply ae_all_iff.mpr
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  exact ae_lt_top' (hm _ hn) (he _ hn).ne

 

theorem mainConclusion_of_lower_and_finiteExpectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ᵐ ω ∂P, Continuous (γ ω))
    (hlo : ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (segment (γ ω) s t))
    (hm : ∀ R : ℝ, 0 < R → AEMeasurable (fun ω => hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 R)) P)
    (he : FiniteExpectedWholeTrace P h γ) : MainConclusion P h γ := by
  constructor
  · have hb := ae_integer_balls_lt_top_of_finiteExpectation P h γ hm he
    filter_upwards [hc, hlo, hb] with ω hcω hloω hbω
    exact mainEvent_of_integer_balls h γ ω hcω hloω hbω
  · intro R hR
    refine ⟨hm R hR, ?_⟩
    refine ⟨(∫⁻ ω, hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 R) ∂P).toNNReal, ?_⟩
    rw [ENNReal.coe_toNNReal (he R hR).ne]

lemma finiteExpectedWholeTrace_of_mainConclusion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) (hc : MainConclusion P h γ) :
    FiniteExpectedWholeTrace P h γ := by
  intro R hR
  obtain ⟨C, hC⟩ := (hc.2 R hR).2
  exact hC.trans_lt ENNReal.coe_lt_top

 

lemma finiteExpectedWholeTrace_iff_integer_balls
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) :
    FiniteExpectedWholeTrace P h γ ↔
      ∀ n : ℕ, (∫⁻ ω, hausdorffGauge h
        (wholeTrace (γ ω) ∩ Metric.closedBall 0 ((n : ℝ) + 1)) ∂P) < ∞ := by
  constructor
  · intro he n
    exact he _ (by positivity)
  · intro he R _hR
    obtain ⟨n, hn⟩ := exists_nat_ge R
    apply lt_of_le_of_lt _ (he n)
    apply lintegral_mono
    intro ω
    apply measure_mono
    exact inter_subset_inter_right _ (Metric.closedBall_subset_closedBall (by linarith))

end SLEExactGauge

 

open MeasureTheory
open scoped ENNReal NNReal
namespace SLEExactGauge

 

theorem mainConclusion_iff_finiteExpectedWholeTrace
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    MainConclusion P h γ ↔ FiniteExpectedWholeTrace P h γ := by
  constructor
  · exact finiteExpectedWholeTrace_of_mainConclusion P h γ
  · intro he
    have hc : ∀ᵐ ω ∂P, Continuous (γ ω) := by
      obtain ⟨B, _hB, hcap⟩ := hSLE.2
      filter_upwards [hcap] with ω hω
      obtain ⟨G, F, hGF⟩ := hω
      exact hGF.1
    apply mainConclusion_of_lower_and_finiteExpectation P h γ hc
      (sourceLowerMain_proved Ω inferInstance P inferInstance κ hκ hκ8 γ hSLE h hh hf)
      _ he
    intro R _hR
    exact source_sle_whole_trace_aemeasurable P κ γ hSLE h hh _ Metric.isClosed_closedBall

end SLEExactGauge

end
end
end

end OAI
