import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExtendLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

lemma localSlope_congr_nhds {f g : X → ℝ} {x : X} (h : f =ᶠ[𝓝 x] g) :
    localSlope f x = localSlope g x := by
  have hx : f x = g x := h.self_of_nhds
  apply Filter.limsup_congr
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  rw [hy,hx]

lemma localSlope_const (c : ℝ) (x : X) : localSlope (fun _ : X => c) x = 0 := by
  simpa [localSlope] using (Filter.limsup_const_bot (f := 𝓝[≠] x) (α := ℝ≥0∞))

lemma localSlope_zero_of_notMem_tsupport {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) :
    localSlope f x = 0 := by
  rw [localSlope_congr_nhds (g := fun _ : X => (0 : ℝ)) ?_,localSlope_const]
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

lemma localSlope_toReal_product_le {f g : X → ℝ} (hf : GloballyLipschitz f)
    (hg : GloballyLipschitz g) (x : X) :
    (localSlope (fun y => f y*g y) x).toReal ≤
      |f x| *(localSlope g x).toReal+|g x| *(localSlope f x).toReal := by
  have H := ENNReal.toReal_mono (show ENNReal.ofReal |f x| *localSlope g x+
      ENNReal.ofReal |g x| *localSlope f x ≠ ∞ by
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hg x),
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hf x)⟩)
    (localSlope_product_le hf.choose_spec hg.choose_spec x)
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hg x))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hf x)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] using H

variable [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_bound {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ∀ x, |(localSlope φ x).toReal| ≤ L := by
  intro x
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hφ x)).trans_eq
    (ENNReal.coe_toReal L)

lemma slopeGraph_localized {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2SlopeGraph ν) :
    WithLp.toLp 2
      (cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) f,
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) D+
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ (localSlope_toReal_bound hφ))
        (realAbs_lipschitz.compLp abs_zero f)) ∈ l2SlopeGraph m := by
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  have hT (u : Lp ℝ 2 ν) : T u =ᵐ[m] (fun x => u x*φ x) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => image_eq_zero_of_notMem_tsupport hx) u
  have hS (u : Lp ℝ 2 ν) : S u =ᵐ[m] (fun x => u x*(localSlope φ x).toReal) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => by rw [localSlope_zero_of_notMem_tsupport hx,ENNReal.toReal_zero]) u
  let p := WithLp.toLp 2 (f,D)
  obtain ⟨u,hu,huν,hup,hDu⟩ := hD
  have hmul : GloballyLipschitz (fun x => φ x*u x) := lipschitz_mul_compact ⟨L,hφ⟩ hu hφc
  have hucoe : ∀ᵐ x ∂ν, p.fst x = u x := by rw [← hup]; exact huν.coeFn_toLp
  have hgcoe : T p.fst =ᵐ[m] (fun x => φ x*u x) := by
    filter_upwards [hT p.fst,(ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hucoe)] with x hx hy
    rw [hx]
    by_cases hxs : x ∈ tsupport φ
    · rw [hy hxs,mul_comm]
    · simp only [image_eq_zero_of_notMem_tsupport hxs,mul_zero,zero_mul]
  have hgm : MemLp (fun x => φ x*u x) 2 m := (Lp.memLp (T p.fst)).ae_eq hgcoe
  refine ⟨_,hmul,hgm,Lp.ext (hgm.coeFn_toLp.trans hgcoe.symm),?_⟩
  filter_upwards [hT p.snd,hS (realAbs_lipschitz.compLp abs_zero p.fst),
    Lp.coeFn_add (T p.snd) (S (realAbs_lipschitz.compLp abs_zero p.fst)),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hDu),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hucoe),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le
        (realAbs_lipschitz.coeFn_compLp abs_zero p.fst))] with x ht hs hadd hd huf hab
  change (localSlope (fun x => φ x*u x) x).toReal ≤
    (T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst)) x
  rw [hadd,Pi.add_apply,ht,hs]
  have H := localSlope_toReal_product_le ⟨L,hφ⟩ hu x
  rw [abs_of_nonneg (hφ0 x)] at H
  by_cases hxs : x ∈ tsupport φ
  · rw [show (realAbs_lipschitz.compLp abs_zero p.fst) x = |u x| from
      (hab hxs).trans (congrArg abs (huf hxs))]
    exact H.trans (add_le_add (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hd hxs) (hφ0 x)) le_rfl)
  · simpa only [image_eq_zero_of_notMem_tsupport hxs,
      localSlope_zero_of_notMem_tsupport hxs,ENNReal.toReal_zero,mul_zero,zero_mul,add_zero]
      using H

omit [MetricSpace X] [BorelSpace X] in
def localizedSlopeGraphMap (T S : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m)
    (p : WithLp 2 (Lp ℝ 2 ν × Lp ℝ 2 ν)) : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
  WithLp.toLp 2 (T p.fst,T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst))

omit [MetricSpace X] [BorelSpace X] in
lemma continuous_localizedSlopeGraphMap (T S : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m) :
    Continuous (localizedSlopeGraphMap T S) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
    ((T.continuous.comp (WithLp.continuous_fst 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))).prodMk
     ((T.continuous.comp (WithLp.continuous_snd 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))).add
      (S.continuous.comp ((realAbs_lipschitz.continuous_compLp abs_zero).comp
        (WithLp.continuous_fst 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))))))

lemma relaxedGraph_localized {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν) :
    WithLp.toLp 2
      (cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) f,
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) D+
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ (localSlope_toReal_bound hφ))
        (realAbs_lipschitz.compLp abs_zero f)) ∈ l2RelaxedGraph m := by
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  let P := localizedSlopeGraphMap T S
  have hP := continuous_localizedSlopeGraphMap T S
  have hraw : l2SlopeGraph ν ⊆ P ⁻¹' l2RelaxedGraph m := by
    intro p hp
    change WithLp.toLp 2 (T p.fst,T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst)) ∈ l2RelaxedGraph m
    apply subset_closure
    exact slopeGraph_localized hφ hφc hφ0 hφB hc hlocal (f := p.fst) (D := p.snd) hp
  have H := closure_minimal hraw (isClosed_l2RelaxedGraph.preimage hP) hD
  exact H
end WeakHessian

end
end InlinedFile0

end OAI
