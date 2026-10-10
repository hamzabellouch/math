import Mathlib
import OAI.Geometry.WeakHessian.Calculus.ControlNorm

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

lemma lsc_real_lintegral_le_liminf {μ : Measure X} {μs : ℕ → Measure X}
    {f : X → ℝ} (hf : LowerSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hopen : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂μs i) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (ae_of_all _ hf0) hf.measurable.aemeasurable]
  calc
    ∫⁻ t in Ioi (0:ℝ), μ {x | t < f x} ≤
        ∫⁻ t in Ioi (0:ℝ), atTop.liminf (fun i => μs i {x | t < f x}) :=
      lintegral_mono fun t => hopen _ (hf.isOpen_preimage t)
    _ ≤ atTop.liminf (fun i => ∫⁻ t in Ioi (0:ℝ), μs i {x | t < f x}) :=
      lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
        measure_mono fun x hx => hst.trans_lt hx))

lemma lsc_lintegral_le_liminf {μ : Measure X} {μs : ℕ → Measure X}
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f)
    (hopen : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf (fun i => ∫⁻ x, f x ∂μs i) := by
  let g : ℕ → ℝ≥0∞ → ℝ := fun n z => (min z (n:ℝ≥0∞)).toReal
  have hfin (n : ℕ) (z : ℝ≥0∞) : min z (n:ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hgcont (n : ℕ) : Continuous (g n) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hc : Continuous (fun w : ℝ≥0∞ => min w (n:ℝ≥0∞)) := continuous_id.min continuous_const
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun w : ℝ≥0∞ => min w (n:ℝ≥0∞))
      (ENNReal.continuousAt_toReal (hfin n z)) hc.continuousAt
  have hgmono (n : ℕ) : Monotone (g n) := fun a b hab =>
    ENNReal.toReal_mono (hfin n b) (min_le_min_right _ hab)
  have H (n : ℕ) : (∫⁻ x, min (f x) (n:ℝ≥0∞) ∂μ) ≤
      atTop.liminf (fun i => ∫⁻ x, f x ∂μs i) := by
    have h := lsc_real_lintegral_le_liminf ((hgcont n).comp_lowerSemicontinuous hf (hgmono n))
      (fun _ => ENNReal.toReal_nonneg) hopen
    have heq : (fun x => ENNReal.ofReal (g n (f x))) = fun x => min (f x) (n:ℝ≥0∞) := by
      ext x
      exact ENNReal.ofReal_toReal (hfin n (f x))
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.trans (liminf_le_liminf (Eventually.of_forall (fun i => lintegral_mono (fun _ => min_le_left _ _))))
  have hsup : (fun x => ⨆ n : ℕ, min (f x) (n:ℝ≥0∞)) = f := by
    ext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, (⨆ n : ℕ, min (f x) (n:ℝ≥0∞)) ∂μ := by rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, min (f x) (n:ℝ≥0∞) ∂μ :=
      lintegral_iSup (fun n => hf.measurable.min measurable_const)
        (fun m n hmn x => min_le_min_left _ (by exact_mod_cast hmn))
    _ ≤ _ := iSup_le H

lemma lsc_lintegral_le_liminf_of_tendsto [PseudoMetrizableSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    ∫⁻ x, f x ∂(μ:Measure X) ≤ atTop.liminf (fun i => ∫⁻ x, f x ∂(μs i:Measure X)) :=
  lsc_lintegral_le_liminf hf (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG)

end WeakHessianTransport

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def kineticAction (γ : Curve X) : ℝ≥0∞ := controlNorm γ ^ 2

lemma lowerSemicontinuous_kineticAction : LowerSemicontinuous (kineticAction (X := X)) :=
  (ENNReal.continuous_pow 2).comp_lowerSemicontinuous lowerSemicontinuous_controlNorm
    (fun _ _ h => pow_le_pow_left₀ (bot_le) h 2)

lemma kineticAction_finite_controlNorm {γ : Curve X} (h : kineticAction γ < ∞) :
    controlNorm γ < ∞ := by
  by_contra hn
  have heq : controlNorm γ = ∞ := top_unique (not_lt.mp hn)
  simp [kineticAction, heq] at h

lemma speed_energy_le_kineticAction (γ : Curve X) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ kineticAction γ := by
  by_cases h : kineticAction γ = ∞
  · simp [h]
  have hn := kineticAction_finite_controlNorm (lt_top_iff_ne_top.mpr h)
  have hB : HasControlBound γ (controlNorm γ).toReal :=
    (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hn.ne])
  obtain ⟨a,ha,haB⟩ := hB.squareControl
  calc
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤
        ∫⁻ t in Icc (0:ℝ) 1, (ENNReal.ofReal (a t))^2 :=
      lintegral_mono_ae (ha.metricSpeed_le.mono fun t ht => pow_le_pow_left₀ (bot_le) ht 2)
    _ = ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((a t)^2) := by
      apply lintegral_congr_ae
      filter_upwards [ha.2.2.1] with t ht
      exact (ENNReal.ofReal_pow ht 2).symm
    _ = ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, (a t)^2) :=
      (ofReal_integral_eq_lintegral_ofReal ha.2.1.integrable_sq (ae_of_all _ (fun t => sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal ((controlNorm γ).toReal^2) := ENNReal.ofReal_le_ofReal haB
    _ = kineticAction γ := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn.ne]; rfl

lemma kineticAction_finite_isAC2 {γ : Curve X} (h : kineticAction γ < ∞) : IsAC2 γ :=
  controlNorm_finite_isAC2 (kineticAction_finite_controlNorm h)

lemma probability_isTight_of_action [CompactSpace X]
    (S : Set (ProbabilityMeasure (Curve X))) {C : ℝ≥0∞} (hC : C < ∞)
    (hS : ∀ π ∈ S, (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C) :
    IsTightMeasureSet {((π : ProbabilityMeasure (Curve X)) : Measure (Curve X)) | π ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [hεtop]⟩
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
  refine ⟨{γ : Curve X | HasControlBound γ R}, isCompact_hasControlBound R, ?_⟩
  rintro μ ⟨π,hπ,rfl⟩
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

lemma exists_action_limit [CompactSpace X]
    (πs : ℕ → ProbabilityMeasure (Curve X)) {C : ℝ≥0∞} (hC : C < ∞)
    (hπs : ∀ n, (∫⁻ γ, kineticAction γ ∂(πs n:Measure (Curve X))) ≤ C) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ C := by
  have htight := probability_isTight_of_action (range πs) hC (by rintro _ ⟨n,rfl⟩; exact hπs n)
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

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

end
end InlinedFile0

end OAI
