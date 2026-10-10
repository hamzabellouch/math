import Mathlib
import OAI.Probability.Perceptron.Variational.ConvexUniform
import OAI.Probability.Perceptron.Variational.GlobalContact
import OAI.Probability.Perceptron.Pressure.PatternFree

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma perturbationScale_tendsto_zero :
    Tendsto (fun n : ℕ => perturbationScale (n+1)) atTop (𝓝 0) := by
  unfold perturbationScale
  convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) using 1
  simp only [neg_div]
  rfl

lemma sourcePatternFree_uniform_upper {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (H : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
      (h : Fin (k+1)→ℝ), h∈sourceStepFieldCap k H →
      ∀ u : Fin (n+1)→ℝ, (∀ j, u j∈Icc 0 2) →
      ∀ q : Fin (k+1)→Time, Monotone q → (q (Fin.last k):ℝ)<1 →
      sourceExpectedPressure n k f p d h (stepCumulative w) 0 u ≤
        finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q+ε := by
  have hs := finiteSphericalFieldValue_compact_uniform w hw hw1
    (sourceStepFieldCap_compact k H) (fun h hh => ⟨hh.2,hh.1.1 0⟩)
  rw [Metric.tendstoUniformlyOn_iff] at hs
  have ht : Tendsto (fun n : ℕ => 8*perturbationScale (n+1)^2) atTop (𝓝 0) := by
    simpa using perturbationScale_tendsto_zero.pow 2 |>.const_mul 8
  filter_upwards [hs (ε/2) (by positivity),ht.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))]
    with n hn hn' f p d h hh u hu q hq hq1
  have hc := sourceExpectedPressure_perturbation_comparison n k f p d h hh.1.1 hh.2
    (stepCumulative w) (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
    (stepCumulative_lt_one w hw hw1) 0 (u := fun _ => 0) (v := u)
    (fun j => ⟨le_rfl,by norm_num⟩) hu
  change |sourceExpectedPressure n k f p d h (stepCumulative w) 0 u-
    sourceExpectedPressure n k f p d h (stepCumulative w) 0 (fun _ => 0)|≤_ at hc
  rw [sourceExpectedPressure_patternFree n k f p d w h hw hw1 hh.2 (hh.1.1 0)] at hc
  obtain ⟨r,hr,hr1,hrmin,-⟩ := finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh.2 (hh.1.1 0)
  have hle := hrmin.2 (show finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q∈
    finiteSphericalDualValues w h (fun i => (hw i).le) hw1 from ⟨q,⟨hq,hq1⟩,rfl⟩)
  have he := hn h hh
  rw [Real.dist_eq,hrmin.csInf_eq] at he
  have hab := (abs_le.mp hc).2
  have hae := (abs_lt.mp he).1
  linarith

lemma sourcePressure_uniform_upper {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (H : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
      (h : Fin (k+1)→ℝ), h∈sourceStepFieldCap k H →
      ∀ u : Fin (n+1)→ℝ, (∀ j, u j∈Icc 0 2) →
      ∀ q : Fin (k+1)→Time, Monotone q → (q (Fin.last k):ℝ)<1 → ∀ t : ℝ≥0,
      sourceExpectedPressure n k f p d h (stepCumulative w) t u ≤
        finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q+ε+(t:ℝ)*‖f‖ := by
  filter_upwards [sourcePatternFree_uniform_upper w hw hw1 H hε] with n hn
  intro f p d h hh u hu q hq hq1 t
  have hc := sourceExpectedPressure_density_comparison n k f p d h (stepCumulative w) u
    (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
    (stepCumulative_lt_one w hw hw1) 0 t
  rw [NNReal.coe_zero,sub_zero,abs_of_nonneg t.coe_nonneg] at hc
  linarith [(abs_le.mp hc).2,hn f p d h hh u hu q hq hq1]

lemma sourceContactObjective_zero_lower {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (H : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
      (q : Fin (k+1)→Time), Monotone q → (q (Fin.last k):ℝ)<1 →
      ∀ δ α (a : SourceContactParameter n k), a∈sourceContactCompactDomain n k α H → a.1=0 →
        -ε ≤ sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a := by
  filter_upwards [sourcePatternFree_uniform_upper w hw hw1 H hε] with n hn
  intro P f p d q hq hq1 δ α a ha ht
  have he := hn f p d a.2.1 ha.2.1 a.2.2
    (fun j => ⟨by linarith [ha.2.2.1 j],ha.2.2.2 j⟩) q hq hq1
  have hpen : 0≤quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2 := by
    unfold quadraticBoxPenalty sourcePenaltyWeight
    positivity
  have hsum : (∑ i, w i*(q i:ℝ)*a.2.1 i)=(∑ i, w i*a.2.1 i*(q i:ℝ)) := by
    apply Finset.sum_congr rfl
    intros
    ring
  unfold sourceStepContactObjective sourceJointPressure
  rw [ht,NNReal.coe_zero,zero_mul,add_zero,hsum]
  unfold finiteSphericalDualObjective at he
  linarith

lemma sourceNegativeContact_positive_density {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (H : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
      (q : Fin (k+1)→Time), Monotone q → (q (Fin.last k):ℝ)<1 →
      ∀ δ α (a : SourceContactParameter n k), a∈sourceContactCompactDomain n k α H →
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a < -ε → 0<a.1 := by
  filter_upwards [sourceContactObjective_zero_lower w hw hw1 H hε] with n hn
  intro P f p d q hq hq1 δ α a ha hneg
  by_contra ht
  have he : a.1=0 := le_antisymm (le_of_not_gt ht) zero_le
  exact (not_le_of_gt hneg) (hn P f p d q hq hq1 δ α a ha he)

lemma sourceContactObjective_uniform_lower {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (H : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
      (q r : Fin (k+1)→Time), Monotone r → (r (Fin.last k):ℝ)<1 →
      ∀ δ α (a : SourceContactParameter n k), a∈sourceContactCompactDomain n k α H →
      (∑ i, w i*((r i:ℝ)-(q i:ℝ))*a.2.1 i)+
        (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-
        (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
        (a.1:ℝ)*(controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ-‖f‖)-ε ≤
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a := by
  filter_upwards [sourcePressure_uniform_upper w hw hw1 H hε] with n hn
  intro P f p d q r hr hr1 δ α a ha
  have he := hn f p d a.2.1 ha.2.1 a.2.2
    (fun j => ⟨by linarith [ha.2.2.1 j],ha.2.2.2 j⟩) r hr hr1 a.1
  have hpen : 0≤quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2 := by
    unfold quadraticBoxPenalty sourcePenaltyWeight
    positivity
  have hsum : (∑ i, w i*((r i:ℝ)-(q i:ℝ))*a.2.1 i)=
      (∑ i, w i*a.2.1 i*(r i:ℝ))-(∑ i, w i*(q i:ℝ)*a.2.1 i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros
    ring
  unfold sourceStepContactObjective sourceJointPressure
  unfold finiteSphericalDualObjective at he
  rw [hsum]
  linarith

lemma sourceNegativeContact_field_interior {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ)
    (q r : Fin (k+1)→Time) (hr : Monotone r) (hr1 : (r (Fin.last k):ℝ)<1)
    {η : ℝ} (hη : 0<η) (hqr : ∀ i, (q i:ℝ)+η≤(r i:ℝ)) (α : ℝ≥0)
    (H : ℝ) (hH : (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
      2*(α:ℝ)*‖f‖ ≤ η*w (Fin.last k)*H) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (p d : Fin (n+1)→ℕ) (δ : ℝ), 0≤δ →
      ∀ a : SourceContactParameter n k, a∈sourceContactCompactDomain n k α H →
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a < -ε →
      a.2.1 (Fin.last k)<H := by
  filter_upwards [sourceContactObjective_uniform_lower w hw hw1 H hε] with n hn
  intro p d δ hδ a ha hneg
  have he := hn P f p d q r hr hr1 δ α a ha
  have hs : (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal≥0 := ENNReal.toReal_nonneg
  have hv := neg_norm_le_controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)
  have ht : -2*(α:ℝ)*‖f‖ ≤
      (a.1:ℝ)*(controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ-‖f‖) := by
    have hm := mul_le_mul_of_nonneg_left (show -2*‖f‖ ≤
      controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ-‖f‖ by linarith) a.1.coe_nonneg
    have ha' : (a.1:ℝ)≤(α:ℝ) := ha.1.2
    nlinarith [mul_le_mul_of_nonneg_right ha' (norm_nonneg f)]
  have hsum : η*w (Fin.last k)*a.2.1 (Fin.last k) ≤
      ∑ i, w i*((r i:ℝ)-(q i:ℝ))*a.2.1 i := by
    apply le_trans _ (Finset.single_le_sum (fun i (_ : i∈Finset.univ) =>
      mul_nonneg (mul_nonneg (hw i).le (by linarith [hqr i])) (ha.2.1.1.1 i)) (Finset.mem_univ (Fin.last k)))
    nlinarith [mul_le_mul_of_nonneg_left (hqr (Fin.last k))
      (mul_nonneg (hw (Fin.last k)).le (ha.2.1.1.1 (Fin.last k)))]
  by_contra hnot
  have hEq : a.2.1 (Fin.last k)=H := le_antisymm (ha.2.1.1.2 (Fin.last k)) (le_of_not_gt hnot)
  rw [hEq] at hsum
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
