import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.FullRank
import OAI.Geometry.IntegralFillings.Charts.Straightening

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {d : ℕ}
lemma coordinate_scalarOn_fderiv {s : Set (Euc d)} {x : Euc d}
    (hu : UniqueDiffWithinAt ℝ s x) (hxs : x ∈ s) {F : Euc d → Euc d}
    (hF : DifferentiableAt ℝ F x) (i : Fin d) :
    fderivWithin ℝ (MetricDifferentiation.scalarOn (fun y : s => F y)
      (EuclideanSpace.proj i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ F x) := by
  apply HasFDerivWithinAt.fderivWithin _ hu
  have hD := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  apply hD.hasFDerivWithinAt.congr
  · intro y hy
    simp only [MetricDifferentiation.scalarOn,dite_eq_left hy,Function.comp_apply]
  · simp only [MetricDifferentiation.scalarOn,dite_eq_left hxs,Function.comp_apply]

theorem exists_replaceMap_pieces {s : Set (Euc d)} (hs : MeasurableSet s)
    (hsf : volume s ≠ (⊤ : ℝ≥0∞)) (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc d)) (J : ℕ → ℝ≥0) (_hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)
          (fun x : t i => replaceMap j g x) ∧
        AntilipschitzWith (J i) (fun x : t i => replaceMap j g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
        fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
  classical
  let F : s → Euc d := fun x => replaceMap j g x
  have hF : LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) F := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    exact (replaceMap_lipschitz j hg).dist_le_mul a b
  obtain ⟨t,J,hts,htm,htd,htb,hzero⟩ :=
    MetricDifferentiation.exists_lipschitz_chart_decomposition hs hsf hF
  refine ⟨t,J,hts,htm,htd,htb,?_⟩
  let π : Fin d → Euc d → ℝ := fun i x => x i
  have hπ (i : Fin d) : ∃ L : ℝ≥0, LipschitzWith L (π i) :=
    ⟨‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖₊,
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).lipschitzWith⟩
  filter_upwards [hzero π hπ,ae_uniqueDiffWithinAt volume s,
    (hg.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hs] with x hx hu hgx hxs hnot
  have he (i : Fin d) : fderivWithin ℝ (MetricDifferentiation.scalarOn F (π i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ (replaceMap j g) x) :=
    coordinate_scalarOn_fderiv hu hxs (replaceMap_hasFDerivAt hgx j).differentiableAt i
  have hd := hx hnot
  simp only [he,ContinuousLinearMap.comp_apply] at hd
  rw [←det_replaceMap_fderiv hgx j]
  exact hd

end SharpIntegralFillings.EuclideanStraightening

namespace SharpIntegralFillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem exists_straightened_pieces {k : ℕ} {s : Set (Euc (k+1))}
    (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {g : Euc (k+1) → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc (k+1))) (dir : ℕ → Fin (k+1)) (J : ℕ → ℝ≥0),
      (∀ i, t i ⊆ s) ∧ (∀ i, MeasurableSet (t i)) ∧
      Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊)
          (fun x : t i => straightenMap (dir i) g x) ∧
        AntilipschitzWith (J i) (fun x : t i => straightenMap (dir i) g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i → fderiv ℝ g x = 0 := by
  classical
  choose t J hts htm _htd htb hz using fun j : Fin (k+1) =>
    exists_replaceMap_pieces hs hsf j hg
  let := Denumerable.ofEncodableOfInfinite (Fin (k+1) × ℕ)
  let e : ℕ ≃ Fin (k+1) × ℕ := (Denumerable.eqv _).symm
  let V : ℕ → Set (Euc (k+1)) := fun i => t (e i).1 (e i).2
  have hsub (i : ℕ) : disjointed V i ⊆ t (e i).1 (e i).2 := disjointed_le V i
  have hcover : (⋃ i, disjointed V i) = ⋃ j, ⋃ l, t j l := by
    rw [iUnion_disjointed]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,(e i).2,hi⟩
    · rintro ⟨j,l,h⟩
      refine ⟨e.symm (j,l),?_⟩
      simpa only [V,e.apply_symm_apply] using h
  refine ⟨disjointed V,fun i => (e i).1,fun i => J (e i).1 (e i).2,
    fun i => (hsub i).trans (hts _ _),
    fun i => MeasurableSet.disjointed (fun l => htm (e l).1 (e l).2) i,
    disjoint_disjointed V,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact (straightenMap_lipschitz (e i).1 hg).dist_le_mul a b
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have h := (htb (e i).1 (e i).2).2.le_mul_dist
        ⟨a,hsub i a.property⟩ ⟨b,hsub i b.property⟩
      simpa only [straightenMap,Function.comp_apply,(switchZero (e i).1).isometry.dist_eq,
        Subtype.dist_eq] using h
  · filter_upwards [ae_all_iff.mpr hz] with x hx hnot
    have h0 (j : Fin (k+1)) : fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
      apply hx j
      intro hj
      apply hnot
      rw [hcover]
      exact mem_iUnion.mpr ⟨j,hj⟩
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (k+1)) ℝ).toBasis.ext
    intro j
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe,
      _root_.zero_apply] using h0 j

end SharpIntegralFillings.EuclideanStraightening
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings

attribute [local instance] Classical.propDecidable

universe u

end SharpIntegralFillings

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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
open BorelCoefficients

end SharpIntegralFillings

end

end OAI
