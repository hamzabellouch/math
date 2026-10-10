import OAI.Analysis.RotationWeights.Concentration

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

def concentratedWeight {X : Type uX} (H : ℕ → X → ℝ) (z : X) (x : X) : ℝ :=
  by classical exact if x = z then 0 else Real.exp (- ∑' i, H i x)

@[simp] lemma concentratedWeight_self {X : Type uX} (H : ℕ → X → ℝ) (z : X) :
    concentratedWeight H z z = 0 := by simp [concentratedWeight]

lemma concentratedWeight_bounds {X : Type uX} (H : ℕ → X → ℝ) (z : X)
    (hH : ∀ i x, 0 ≤ H i x) (x : X) :
    0 ≤ concentratedWeight H z x ∧ concentratedWeight H z x ≤ 1 := by
  classical
  unfold concentratedWeight
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (tsum_nonneg (fun i ↦ hH i x)))⟩

@[simp] lemma concentratedWeight_eq_zero {X : Type uX} (H : ℕ → X → ℝ) (z x : X) :
    concentratedWeight H z x = 0 ↔ x = z := by
  classical
  unfold concentratedWeight
  split_ifs with h
  · simp [h]
  · simp [h, Real.exp_ne_zero]

def LocallyFiniteOff {X : Type uX} [TopologicalSpace X] (H : ℕ → X → ℝ) (z : X) : Prop :=
  ∀ x, x ≠ z → ∃ s : Finset ℕ, ∀ᶠ y in 𝓝 x, ∀ i, i ∉ s → H i y = 0

lemma finite_support_of_locallyFiniteOff {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hlocal : LocallyFiniteOff H z) {x : X} (hx : x ≠ z) :
    (Function.support (fun i ↦ H i x)).Finite := by
  obtain ⟨s,hs⟩ := hlocal x hx
  exact s.finite_toSet.subset (by
    intro i hi
    by_contra his
    exact hi (mem_of_mem_nhds hs i his))

lemma concentratedWeight_continuousAt_off {X : Type uX} [TopologicalSpace X] [T1Space X]
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i))
    (hlocal : LocallyFiniteOff H z) {x : X} (hx : x ≠ z) :
    ContinuousAt (concentratedWeight H z) x := by
  classical
  obtain ⟨s,hs⟩ := hlocal x hx
  have he : concentratedWeight H z =ᶠ[𝓝 x] (fun y ↦ Real.exp (-∑ i ∈ s, H i y)) := by
    filter_upwards [hs, isOpen_compl_singleton.mem_nhds hx] with y hy hyz
    change y ≠ z at hyz
    rw [concentratedWeight, ite_eq_right hyz]
    congr 2
    exact tsum_eq_sum (fun i hi ↦ hy i hi)
  exact ((continuous_finsetSum s (fun i _ ↦ hc i)).neg.rexp.continuousAt).congr_of_eventuallyEq he

lemma concentratedWeight_le_finite {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z) (s : Finset ℕ) (x : X) :
    concentratedWeight H z x ≤ Real.exp (-∑ i ∈ s, H i x) := by
  classical
  by_cases hx : x = z
  · simp only [concentratedWeight, ite_eq_left hx]
    exact (Real.exp_pos _).le
  rw [concentratedWeight, ite_eq_right hx]
  apply Real.exp_le_exp.mpr
  apply _root_.neg_le_neg
  exact Summable.sum_le_tsum s (fun i _ ↦ hH i x)
    (summable_of_hasFiniteSupport (finite_support_of_locallyFiniteOff H z hlocal hx))

theorem continuous_concentratedWeight {X : Type uX} [TopologicalSpace X] [T1Space X]
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i)) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) :
    Continuous (concentratedWeight H z) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = z
  · subst x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s,hs⟩ := hdiv (-Real.log ε)
    have he : Real.exp (-∑ i ∈ s, H i z) < ε := by
      rw [← Real.exp_log hε]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hev : ∀ᶠ x in 𝓝 z, Real.exp (-∑ i ∈ s, H i x) < ε :=
      ((continuous_finsetSum s (fun i _ ↦ hc i)).neg.rexp.continuousAt).eventually (gt_mem_nhds he)
    filter_upwards [hev] with x hx
    rw [concentratedWeight_self, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_nonneg (concentratedWeight_bounds H z hH x).1]
    exact (concentratedWeight_le_finite H z hH hlocal s x).trans_lt hx
  · exact concentratedWeight_continuousAt_off H z hc hlocal hx

lemma negativeLog_concentratedWeight {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) (x : X) :
    negativeLog (concentratedWeight H z x) = ∑' i, ENNReal.ofReal (H i x) := by
  classical
  by_cases hx : x = z
  · subst x
    rw [concentratedWeight_self, negativeLog, ite_eq_left rfl]
    symm
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro b
    obtain ⟨s,hs⟩ := hdiv b
    calc
      (b : ℝ≥0∞) ≤ ENNReal.ofReal (∑ i ∈ s, H i z) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hs.le
      _ = ∑ i ∈ s, ENNReal.ofReal (H i z) := ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hH i z)
      _ ≤ ∑' i, ENNReal.ofReal (H i z) := ENNReal.sum_le_tsum s
  · rw [negativeLog, ite_eq_right ((concentratedWeight_eq_zero H z x).not.mpr hx),
      concentratedWeight, ite_eq_right hx, Real.log_exp, neg_neg]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i ↦ hH i x)
      (summable_of_hasFiniteSupport (finite_support_of_locallyFiniteOff H z hlocal hx))

theorem lintegral_negativeLog_concentratedWeight {X : Type uX} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i)) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) :
    (∫⁻ x, negativeLog (concentratedWeight H z x) ∂μ) =
      ∑' i, ∫⁻ x, ENNReal.ofReal (H i x) ∂μ := by
  simp_rw [negativeLog_concentratedWeight H z hH hlocal hdiv]
  exact lintegral_tsum (fun i ↦ ((hc i).measurable.ennreal_ofReal).aemeasurable)

lemma locallyFiniteOff_of_shrinking_supports {X : Type uX} [MetricSpace X]
    (H : ℕ → X → ℝ) (z : X) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hs : ∀ i x, r i ≤ dist x z → H i x = 0) : LocallyFiniteOff H z := by
  classical
  intro x hx
  have hd : 0 < dist x z := dist_pos.mpr hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds (half_pos hd)))
  refine ⟨Finset.range N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (half_pos hd)] with y hy
  intro i hi
  apply hs
  have hn : N ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
  have hlt := hN i hn
  have htri := dist_triangle x y z
  have hxy : dist x y < dist x z / 2 := by
    simpa only [Metric.mem_ball, dist_comm y x] using hy
  linarith

lemma ae_finite_support_of_support_measure_sum {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) (w : ℕ → X → ℝ)
    (hw : (∑' i, μ {x | w i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i ↦ w i x)).Finite :=
  ae_finite_setOfPred_mem hw

theorem concentrated_coboundary {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (H G w : ℕ → X → ℝ) (z : X) (hz : μ {z} = 0)
    (hwm : ∀ i, Measurable (w i))
    (hG : (∑' i, μ {x | G i x ≠ 0}) ≠ ∞)
    (hw : (∑' i, μ {x | w i x ≠ 0}) ≠ ∞)
    (hid : ∀ᵐ x ∂μ, ∀ i, H i x - G i x = w i (σ x) - w i x) :
    ∃ a : X → ℝ, Measurable a ∧ (∀ x, 0 < a x) ∧
      ∀ᵐ x ∂μ, concentratedWeight H z x =
        Real.exp (-∑' i, G i x) * a x / a (σ x) := by
  classical
  let b : X → ℝ := fun x ↦ ∑' i, w i x
  let a : X → ℝ := fun x ↦ Real.exp (b x)
  refine ⟨a, (Measurable.tsum hwm).exp, (fun x ↦ Real.exp_pos _), ?_⟩
  have hfin := ae_finite_support_of_support_measure_sum μ w hw
  have hfinσ := hσ.quasiMeasurePreserving.ae hfin
  have hfinG := ae_finite_support_of_support_measure_sum μ G hG
  have hne : ∀ᵐ x ∂μ, x ≠ z := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hz
  filter_upwards [hfin, hfinσ, hfinG, hid, hne] with x hx hxσ hxG hix hxz
  have hsw : Summable (fun i ↦ w i x) := summable_of_hasFiniteSupport hx
  have hswσ : Summable (fun i ↦ w i (σ x)) := summable_of_hasFiniteSupport hxσ
  have hsG : Summable (fun i ↦ G i x) := summable_of_hasFiniteSupport hxG
  have he : (fun i ↦ H i x) = (fun i ↦ G i x + (w i (σ x) - w i x)) := by
    funext i
    linarith [hix i]
  have ht : (∑' i, H i x) = (∑' i, G i x) + (b (σ x) - b x) := by
    rw [he, hsG.tsum_add (hswσ.sub hsw), hswσ.tsum_sub hsw]
  rw [concentratedWeight, ite_eq_right hxz, ht]
  change Real.exp _ = Real.exp _ * Real.exp (b x) / Real.exp (b (σ x))
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring



end ContinuousCircleWeight

end

end OAI
