import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.BorelAction

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in

lemma toL1_mul_dist_le {f g b : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) :
    ‖(hf.mul_bdd hb hM).toL1 (fun x => f x * b x) -
      (hg.mul_bdd hb hM).toL1 (fun x => g x * b x)‖ ≤
      M * ‖hf.toL1 f - hg.toL1 g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))
      ((hg.mul_bdd hb hM).toL1 (fun x => g x * b x)),
    (hf.mul_bdd hb hM).coeFn_toL1, (hg.mul_bdd hb hM).coeFn_toL1,
    Lp.coeFn_sub (hf.toL1 f) (hg.toL1 g), hf.coeFn_toL1, hg.coeFn_toL1, hM]
    with x hsub hfb hgb hsub' hfx hgx hMx
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub, hfb, hgb, hsub', hfx, hgx, ← sub_mul, norm_mul]
  nlinarith [norm_nonneg (f x - g x)]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma tendsto_toL1_mul {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {f b : X → ℝ}
    (hfs : ∀ j, Integrable (fs j) μ) (hf : Integrable f μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    (hlim : Tendsto (fun j => (hfs j).toL1 (fs j)) l (𝓝 (hf.toL1 f))) :
    Tendsto (fun j => ((hfs j).mul_bdd hb hM).toL1 (fun x => fs j x * b x)) l
      (𝓝 ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => toL1_mul_dist_le μ (hfs j) hf hb hM)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul M

lemma borelAction_locality_mul (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f b : X → ℝ} (hf : Integrable f μ) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧
      Function.support b ⊆ U ∧ ∀ x ∈ U, π i x = c) :
    borelAction μ hT (fun x => f x * b x) π = 0 := by
  obtain ⟨M, hM⟩ := hb.2
  have hbM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hM x
  have hbmeas := hb.continuous.aestronglyMeasurable (μ := μ)
  obtain ⟨as, has, halim⟩ := mem_closure_iff_seq_limit.mp (lipToL1_dense μ (hf.toL1 f))
  choose fs hfs using has
  have hnorm : Tendsto (fun j => lipToL1 μ (fs j)) atTop (𝓝 (hf.toL1 f)) := by
    simpa only [hfs] using halim
  have hLp (j) : (integrable_boundedLip μ (fs j).property).toL1 (fs j).val =
      lipToL1 μ (fs j) := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (fs j).val).symm
  have hnorm' : Tendsto (fun j => (integrable_boundedLip μ (fs j).property).toL1 (fs j).val)
      atTop (𝓝 (hf.toL1 f)) := by simpa only [hLp] using hnorm
  have hprod := tendsto_toL1_mul μ (fun j => integrable_boundedLip μ (fs j).property)
    hf hbmeas hbM hnorm'
  have hact := (l1Action μ hT π hπ).continuous.continuousAt.tendsto.comp hprod
  have hz (j) : l1Action μ hT π hπ
      (((integrable_boundedLip μ (fs j).property).mul_bdd hbmeas hbM).toL1
        (fun x => (fs j).val x * b x)) = 0 := by
    rw [← borelAction_of_integrable μ hT _ π hπ,
      borelAction_eq μ hT hμ ⟨(fs j).property.mul hb, hπ⟩]
    apply hT.locality _ _ ⟨(fs j).property.mul hb, hπ⟩
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    refine ⟨i, U, c, hU, ?_, hc⟩
    intro x hx
    apply hbU
    change b x ≠ 0
    intro hbx
    exact hx (by simp only [hbx, mul_zero])
  have heq : l1Action μ hT π hπ ((hf.mul_bdd hbmeas hbM).toL1 (fun x => f x * b x)) = 0 :=
    tendsto_nhds_unique hact (by simpa only [Function.comp_def, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rwa [borelAction_of_integrable μ hT (hf.mul_bdd hbmeas hbM) π hπ]

lemma borelAction_linearCoord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k)
    (g : X → ℝ) (hg : ∃ K : ℝ≥0, LipschitzWith K g) (a c : ℝ) :
    borelAction μ hT b (Function.update π i (fun x => a * π i x + c * g x)) =
      a * borelAction μ hT b π + c * borelAction μ hT b (Function.update π i g) := by
  have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hg
    · simpa only [Function.update_of_ne hji] using hπ j
  have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
    obtain ⟨K, hK⟩ := hπ i
    obtain ⟨L, hL⟩ := hg
    exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
  have hπac : ∀ j, ∃ K : ℝ≥0,
      LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hac
    · simpa only [Function.update_of_ne hji] using hπ j
  have heq : (fun f : Lp ℝ 1 μ =>
      l1Action μ hT (Function.update π i (fun x => a * π i x + c * g x)) hπac f) =
      (fun f => a * l1Action μ hT π hπ f +
        c * l1Action μ hT (Function.update π i g) hπg f) := by
    apply (lipToL1_dense μ).equalizer
    · exact (l1Action μ hT _ _).continuous
    · exact ((l1Action μ hT π hπ).continuous.const_mul a).add
        ((l1Action μ hT _ _).continuous.const_mul c)
    · funext f
      simp only [Function.comp_apply, l1Action_eq μ hT hμ]
      exact hT.linearCoord _ _ i g a c ⟨f.property, hπ⟩ hg
  simpa only [borelAction_of_integrable μ hT hb _ hπac,
    borelAction_of_integrable μ hT hb _ hπ,
    borelAction_of_integrable μ hT hb _ hπg] using congrFun heq (hb.toL1 b)

noncomputable def weightedCurrent (hT : IsMetricCurrent T) (b : X → ℝ) : Functional X k :=
  fun f π => if Admissible f π then borelAction μ hT (fun x => b x * f x) π else 0

lemma weightedCurrent_isMetricCurrent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) {M : ℝ≥0} (hM : ∀ᵐ x ∂μ, |b x| ≤ M) :
    IsMetricCurrent (weightedCurrent μ hT b) := by
  have hprod {f : X → ℝ} (hf : BoundedLip f) : Integrable (fun x => b x * f x) μ := by
    obtain ⟨N, hN⟩ := hf.2
    exact hb.mul_bdd hf.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hN x)
  have hap {f : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible f π) :
      weightedCurrent μ hT b f π = borelAction μ hT (fun x => b x * f x) π := ite_eq_left h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f π h
    exact ite_eq_right h
  · intro f g π a c hf hg hπ
    rw [hap ⟨(hf.const_mul a).add (hg.const_mul c), hπ⟩,
      hap ⟨hf, hπ⟩, hap ⟨hg, hπ⟩]
    have heq : (fun x => b x * (a * f x + c * g x)) =
        a • (fun x => b x * f x) + c • (fun x => b x * g x) := by funext x; simp; ring
    rw [heq, borelAction_add μ hT ((hprod hf).smul a) ((hprod hg).smul c) π hπ,
      borelAction_smul μ hT (hprod hf) π a hπ,
      borelAction_smul μ hT (hprod hg) π c hπ]
  · intro f π i g a c h hg
    have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hg
      · simpa only [Function.update_of_ne hji] using h.2 j
    have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
      obtain ⟨K, hK⟩ := h.2 i
      obtain ⟨L, hL⟩ := hg
      exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
    have hπac : ∀ j, ∃ K : ℝ≥0,
        LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hac
      · simpa only [Function.update_of_ne hji] using h.2 j
    rw [hap ⟨h.1, hπac⟩, hap h, hap ⟨h.1, hπg⟩]
    exact borelAction_linearCoord μ hT hμ (hprod h.1) π h.2 i g hg a c
  · intro f π πs hf hLip hpt
    choose K hK using hLip
    have hπ (i) : LipschitzWith (K i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
    simp only [hap ⟨hf, fun i => ⟨K i, hK i _⟩⟩, hap ⟨hf, fun i => ⟨K i, hπ i⟩⟩]
    exact borelAction_sequentialContinuity μ hT hμ (hprod hf) π πs
      (fun i => ⟨K i, hK i⟩) hpt
  · intro f π h hloc
    rw [hap h]
    exact borelAction_locality_mul μ hT hμ hb h.1 π h.2 hloc
  · have hfin : IsFiniteMeasure ((M : ℝ≥0∞) • μ) := by
      constructor
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ univ)
    refine ⟨(M : ℝ≥0∞) • μ, hfin, ?_⟩
    intro f π hf hπ
    rw [hap ⟨hf, fun i => ⟨1, hπ i⟩⟩,
      integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    have hbound := borelAction_bound μ hT hμ (hprod hf) π (fun _ => 1) hπ
    simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at hbound
    apply hbound.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hprod hf).abs ((integrable_boundedLip μ hf).abs.const_mul M)
    filter_upwards [hM] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BorelCoefficients

attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
