import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Charts.Scalar
import OAI.Geometry.CAT0Fillings.Prism.Chart

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma prism_scalar_eq {f : ℝ × X → ℝ} {p : ℝ × Euc k}
    (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain) :
    C.prism.scalar f ((Prism.split k).symm p) = f (p.1,C.param ⟨p.2,hp.2⟩) := by
  have hz : (Prism.split k).symm p ∈ C.prism.domain := by
    simpa only [prism,prismDomain,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  rw [C.prism.scalar_eq hz]
  change f (C.prismParam _) = _
  simp only [prismParam,ContinuousLinearEquiv.apply_symm_apply]

lemma prism_scalar_extension {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ G : ℝ × Euc k → ℝ, (∃ L, LipschitzWith L G) ∧
      ∀ p (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain),
        G p = f (p.1,C.param ⟨p.2,hp.2⟩) := by
  obtain ⟨L,U,hC,hU⟩ := C.prism.bilipschitz
  obtain ⟨F,hF,heq⟩ := (C.prism.scalar_lipschitzOn hC hf).extend_real
  refine ⟨F ∘ (Prism.split k).symm,⟨_,hF.comp (Prism.split k).symm.lipschitzWith⟩,?_⟩
  intro p hp
  have hz : (Prism.split k).symm p ∈ C.prism.domain := by
    simpa only [prism,prismDomain,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  exact (heq hz).symm.trans (C.prism_scalar_eq hp)

lemma prism_fderiv_decompose {f : ℝ × X → ℝ} {G : ℝ × Euc k → ℝ}
    (heq : ∀ p (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain),
      G p = f (p.1,C.param ⟨p.2,hp.2⟩))
    {p : ℝ × Euc k} (ht : p.1 ∈ Ioo (0:ℝ) 1) (hz : p.2 ∈ C.domain)
    (hG : DifferentiableAt ℝ G p)
    (hu : UniqueDiffWithinAt ℝ C.domain p.2)
    (hup : UniqueDiffWithinAt ℝ C.prism.domain ((Prism.split k).symm p)) :
    (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single 0 1) = deriv (fun t => f (t,C.param ⟨p.2,hz⟩)) p.1 ∧
    (∀ j : Fin k,
      (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j.succ 1) =
      (fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2)
        (EuclideanSpace.single j 1)) := by
  have hfp : fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p) =
      (fderiv ℝ G p).comp (Prism.split k).toContinuousLinearMap := by
    apply HasFDerivWithinAt.fderivWithin _ hup
    have hd := hG.hasFDerivAt.comp ((Prism.split k).symm p) (Prism.split k).hasFDerivAt
    apply hd.hasFDerivWithinAt.congr
    · intro w hw
      have hm : Prism.split k w ∈ Icc (0:ℝ) 1 ×ˢ C.domain := hw
      rw [Function.comp_apply,heq _ hm,C.prism.scalar_eq hw]
      rfl
    · rw [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply,
        C.prism_scalar_eq ⟨Ioo_subset_Icc_self ht,hz⟩,heq _ ⟨Ioo_subset_Icc_self ht,hz⟩]
  have hft : HasDerivAt (fun t => f (t,C.param ⟨p.2,hz⟩))
      ((fderiv ℝ G p) (1,0)) p.1 := by
    have hd := hG.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    apply hd.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with t ht
    exact (heq (t,p.2) ⟨ht,hz⟩).symm
  have hfx : fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2 =
      (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ (Euc k)) := by
    have hd := hG.hasFDerivAt.comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    apply HasFDerivWithinAt.fderivWithin _ hu
    apply hd.hasFDerivWithinAt.congr
    · intro z hz
      rw [C.scalar_eq hz]
      exact (heq (p.1,z) ⟨Ioo_subset_Icc_self ht,hz⟩).symm
    · rw [C.scalar_eq hz]
      exact (heq p ⟨Ioo_subset_Icc_self ht,hz⟩).symm
  constructor
  · rw [hfp,ContinuousLinearMap.comp_apply]
    change (fderiv ℝ G p) (Prism.split k (EuclideanSpace.single 0 1)) = _
    rw [Prism.split_single_zero,hft.deriv]
  · intro j
    rw [hfp,hfx,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
    change (fderiv ℝ G p) (Prism.split k (EuclideanSpace.single j.succ 1)) = _
    rw [Prism.split_single_succ]
    rfl

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma prism_split_measurePreserving :
    MeasurePreserving (Prism.split k).symm
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain))
      (volume.restrict C.prism.domain) := by
  rw [Measure.prod_restrict]
  exact MeasurePreserving.symm (Prism.split k).toHomeomorph.toMeasurableEquiv
    ((Prism.split_measurePreserving k).restrict_preimage (measurableSet_Icc.prod C.borel))

lemma ae_prism_fderiv_decompose {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
    (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single 0 1) =
      deriv (fun t => C.scalar (fun x => f (t,x)) p.2) p.1 ∧
    (∀ j : Fin k,
      (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j.succ 1) =
      (fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2)
        (EuclideanSpace.single j 1)) := by
  obtain ⟨G,⟨L,hG⟩,heq⟩ := C.prism_scalar_extension hf
  have hd : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      DifferentiableAt ℝ G p := by
    rw [Measure.prod_restrict]
    exact ae_restrict_le (hG.ae_differentiableAt
      (μ := (volume : Measure ℝ).prod (volume : Measure (Euc k))))
  have ht : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), t ∈ Ioo (0:ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  have hpt := Measure.quasiMeasurePreserving_fst (ν := volume.restrict C.domain) |>.ae ht
  have hpu := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_uniqueDiffWithinAt volume C.domain)
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  have hpp := C.prism_split_measurePreserving.quasiMeasurePreserving.ae
    (ae_uniqueDiffWithinAt volume C.prism.domain)
  filter_upwards [hd,hpt,hpu,hpz,hpp] with p hd ht hu hz hup
  have h := C.prism_fderiv_decompose heq ht hz hd hu hup
  convert h using 2
  congr 1
  funext t
  exact C.scalar_eq hz

lemma ae_prism_jacobian_decompose (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      C.prism.jacobian π ((Prism.split k).symm p) =
        ∑ i : Fin (k+1), (-1:ℝ)^i.val *
          deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1 *
          C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2 := by
  have h := ae_all_iff.mpr fun i => C.ae_prism_fderiv_decompose (hπ i).choose_spec
  filter_upwards [h] with p hp
  change Matrix.det (Matrix.of (fun i j =>
    (fderivWithin ℝ (C.prism.scalar (π i)) C.prism.domain ((Prism.split k).symm p))
      (EuclideanSpace.single j 1))) = _
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hp i).1]
  congr 1
  apply congrArg Matrix.det
  ext j l
  exact (hp (i.succAbove j)).2 l

end CAT0Fillings.IntegerChart

end
end

end OAI
