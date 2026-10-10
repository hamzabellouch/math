import Mathlib
import OAI.Geometry.WeakHessian.Transport.KineticAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

lemma isCompact_anchoredControl [ProperSpace X] [Nonempty X]
    {K : Set X} (hK : IsCompact K) (B : ℝ) :
    IsCompact {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K} := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall o
  let e := ContinuousMap.isometryEquivBoundedOfCompact Time X
  let A : Set (Time →ᵇ X) := e.symm ⁻¹' {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K}
  have hcl : IsClosed A := ((isClosed_hasControlBound B).inter
    (hK.isClosed.preimage (continuous_eval_const timeZero))).preimage e.symm.continuous
  have heq : Equicontinuous ((↑) : A → Time → X) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => Real.sqrt r*|B|)
    · simpa using (Real.continuous_sqrt.tendsto 0).mul_const |B|
    · intro s t γ
      exact γ.2.1.dist_le_modulus s t
  have hin (f : Time →ᵇ X) (t : Time) (hf : f ∈ A) : f t ∈ Metric.closedBall o (R+|B|) := by
    change HasControlBound (e.symm f) B ∧ (e.symm f) timeZero ∈ K at hf
    have H := hf.1.dist_le_modulus t timeZero
    have ht : dist t timeZero ≤ 1 := by
      change |(t:ℝ)-0| ≤ 1
      rw [sub_zero,abs_of_nonneg t.2.1]
      exact t.2.2
    have hd : dist (f t) (f timeZero) ≤ |B| := by
      apply H.trans
      have hh := Real.sqrt_le_sqrt ht
      simpa only [Real.sqrt_one,one_mul] using mul_le_mul_of_nonneg_right hh (abs_nonneg B)
    have hzero : dist (f timeZero) o ≤ R := hR hf.2
    exact (dist_triangle (f t) (f timeZero) o).trans (by linarith)
  have hc := BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall o (R+|B|))
    (isCompact_closedBall o _) A hcl hin heq
  have H := hc.image e.symm.continuous
  have he : e.symm '' A = {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K} :=
    e.symm.toEquiv.image_preimage _
  rwa [he] at H

lemma exists_action_uniform_tail
    (S : Set (ProbabilityMeasure (Curve X))) {C : ℝ≥0∞} (hC : C < ∞)
    (hS : ∀ π ∈ S, (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C) :
    ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
      ∃ R : ℝ, ∀ π ∈ S, (π:Measure (Curve X)) {γ | HasControlBound γ R}ᶜ ≤ ε := by
  intro ε hε hεtop
  have hdiv : C/ε ≠ ∞ := ENNReal.div_ne_top hC.ne hε.ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hdiv
  let R : ℝ := (n:ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRne : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hRfin : ENNReal.ofReal R ≠ ∞ := ENNReal.ofReal_ne_top
  have hquo : C/ε ≤ (ENNReal.ofReal R)^2 := by
    have h1 : C/ε ≤ ENNReal.ofReal R := by
      apply hn.le.trans
      simp only [R, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
      exact le_add_right le_rfl
    have h2 : (1:ℝ≥0∞) ≤ ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      dsimp [R]
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact h1.trans (by simpa only [pow_two, mul_one] using mul_le_mul_right h2 (ENNReal.ofReal R))
  have hquot : C/(ENNReal.ofReal R)^2 ≤ ε := by
    apply (ENNReal.div_le_iff (pow_ne_zero _ hRne) (ENNReal.pow_ne_top hRfin)).mpr
    have hc := (ENNReal.div_le_iff hε.ne' hεtop).mp hquo
    simpa only [mul_comm] using hc
  refine ⟨R,?_⟩
  intro π hπ
  calc
    (π:Measure (Curve X)) {γ : Curve X | HasControlBound γ R}ᶜ ≤
        (π:Measure (Curve X)) {γ | (ENNReal.ofReal R)^2 ≤ kineticAction γ} := by
      apply measure_mono
      intro γ hγ
      have hnot : ¬ controlNorm γ ≤ ENNReal.ofReal R :=
        fun h => hγ ((controlNorm_le_iff hR.le).mp h)
      exact pow_le_pow_left₀ (bot_le) (le_of_not_ge hnot) 2
    _ ≤ (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X)))/(ENNReal.ofReal R)^2 :=
      meas_ge_le_lintegral_div lowerSemicontinuous_kineticAction.measurable.aemeasurable
        (pow_ne_zero _ hRne) (ENNReal.pow_ne_top hRfin)
    _ ≤ C/(ENNReal.ofReal R)^2 := ENNReal.div_le_div_right (hS π hπ) _
    _ ≤ ε := hquot

variable [MeasurableSpace X] [BorelSpace X]

lemma probability_isTight_of_action_initial [ProperSpace X] [Nonempty X]
    (S : Set (ProbabilityMeasure (Curve X))) {C : ℝ≥0∞} (hC : C < ∞)
    (hS : ∀ π ∈ S, (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C)
    (ht : IsTightMeasureSet {((π:Measure (Curve X)).map (fun γ => γ timeZero)) | π ∈ S}) :
    IsTightMeasureSet {((π:Measure (Curve X))) | π ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht ⊢
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [htop]⟩
  have hhalf : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hft : ε/2 ≠ ∞ := ENNReal.div_ne_top htop (by norm_num)
  obtain ⟨R,hR⟩ := exists_action_uniform_tail S hC hS (ε/2) hhalf hft
  obtain ⟨K,hK,hKm⟩ := ht (ε/2) hhalf
  refine ⟨{γ : Curve X | HasControlBound γ R ∧ γ timeZero ∈ K},
    isCompact_anchoredControl hK R,?_⟩
  rintro μ ⟨π,hπ,rfl⟩
  have hi : (π:Measure (Curve X)) ((fun γ => γ timeZero) ⁻¹' K)ᶜ ≤ ε/2 := by
    have H := hKm _ ⟨π,hπ,rfl⟩
    rwa [Measure.map_apply (continuous_eval_const timeZero).measurable hK.measurableSet.compl] at H
  calc
    (π:Measure (Curve X)) {γ | HasControlBound γ R ∧ γ timeZero ∈ K}ᶜ =
        (π:Measure (Curve X)) ({γ | HasControlBound γ R}ᶜ ∪ ((fun γ => γ timeZero) ⁻¹' K)ᶜ) := by
      congr 1
      ext γ
      simp only [mem_compl_iff,mem_ofPred_eq,not_and_or,mem_union,mem_preimage]
    _ ≤ (π:Measure (Curve X)) {γ | HasControlBound γ R}ᶜ +
        (π:Measure (Curve X)) ((fun γ => γ timeZero) ⁻¹' K)ᶜ := measure_union_le _ _
    _ ≤ ε/2+ε/2 := add_le_add (hR π hπ) hi
    _ = ε := ENNReal.add_halves ε

lemma exists_action_limit_initial [ProperSpace X] [Nonempty X]
    (πs : ℕ → ProbabilityMeasure (Curve X)) {C : ℝ≥0∞} (hC : C < ∞)
    (hπs : ∀ n, (∫⁻ γ, kineticAction γ ∂(πs n:Measure (Curve X))) ≤ C)
    (ht : IsTightMeasureSet {((πs n:Measure (Curve X)).map (fun γ => γ timeZero)) | n : ℕ}) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ C := by
  have ht' : IsTightMeasureSet {((π:Measure (Curve X)).map (fun γ => γ timeZero)) | π ∈ range πs} := by
    convert ht using 1
    ext μ
    simp
  have htight := probability_isTight_of_action_initial (range πs) hC
    (by rintro _ ⟨n,rfl⟩; exact hπs n) ht'
  obtain ⟨π,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hbound : (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C := by
    have H := WeakHessianTransport.lsc_lintegral_le_liminf_of_tendsto hlim lowerSemicontinuous_kineticAction
    exact H.trans (liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall (fun n => hπs (φ n)))))
  refine ⟨π,φ,hφ,hlim,hbound,?_,?_⟩
  · have hfinite := ae_lt_top lowerSemicontinuous_kineticAction.measurable (hbound.trans_lt hC).ne
    exact hfinite.mono fun γ hγ => kineticAction_finite_isAC2 hγ
  · exact (lintegral_mono speed_energy_le_kineticAction).trans hbound
end WeakHessian

end

end OAI
