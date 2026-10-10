import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SmoothDistance

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance tangentLiftNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tangentLiftNormedAddCommGroupEndomorphism : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceEndomorphism : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance tangentLiftNormedAddCommGroupDual : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceDual : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance tangentLiftNormedAddCommGroupBilinear : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceBilinear : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

def coordinateTangentLift (φ : E → E) (z : E × E) : E × E :=
  (φ z.1, fderiv ℝ φ z.1 z.2)

lemma fderiv_coordinateTangentLift {φ : E → E} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x)
    (v u w : E) :
    fderiv ℝ (coordinateTangentLift φ) (x,v) (u,w) =
      (fderiv ℝ φ x u, fderiv ℝ (fderiv ℝ φ) x u v + fderiv ℝ φ x w) := by
  have h1 := hφ.hasFDerivAt.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hDφ.hasFDerivAt.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ))
  have he := congrArg (fun L : (E × E) →L[ℝ] (E × E) => L (u,w)) (h1.prodMk h2).fderiv
  change fderiv ℝ (fun y : E × E => (φ y.1, fderiv ℝ φ y.1 y.2)) (x,v) (u,w) = _
  convert he using 1 <;> simp [add_comm]

lemma coordinateTangentLift_push_geodesicField
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x v : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x) (hφs : Function.Surjective (fderiv ℝ φ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) :
    fderiv ℝ (coordinateTangentLift φ) (x,v) (coordinateGeodesicField g (x,v)) =
      coordinateGeodesicField h (coordinateTangentLift φ (x,v)) := by
  have hpd := hφ.differentiableAt (by simp)
  have hD := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heq := christoffel_pushforward hg hh hφ hφs hmetric hgi hhi hhs v v
  change fderiv ℝ (coordinateTangentLift φ) (x,v) (v,-coordinateChristoffel g x v v) = _
  rw [fderiv_coordinateTangentLift hpd hD]
  apply Prod.ext
  · rfl
  · change fderiv ℝ (fderiv ℝ φ) x v v + fderiv ℝ φ x (-coordinateChristoffel g x v v) =
      -coordinateChristoffel h (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x v)
    rw [map_neg,heq]
    abel

end

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance tangentLiftNormedAddCommGroupCotangent (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceCotangent (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance tangentLiftContinuousAddCotangent : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance
local instance tangentLiftContinuousSMulCotangent : ∀ x : M, ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance

def riemannianCoordinateMetric (a : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let y := (extChartAt 𝓘(ℝ,E) a).symm z
  let L := (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y
  (innerSL ℝ (E := TangentSpace 𝓘(ℝ,E) y)).bilinearComp L L

lemma riemannianCoordinateMetric_apply (a : M) (z u v : E) :
    riemannianCoordinateMetric a z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) v) := rfl

lemma riemannianCoordinateMetric_symm (a : M) (z u v : E) :
    riemannianCoordinateMetric a z u v = riemannianCoordinateMetric a z v u :=
by
  simp only [riemannianCoordinateMetric_apply]
  exact real_inner_comm _ _

lemma riemannianCoordinateMetric_positive {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target) {v : E} (hv : v ≠ 0) :
    0 < riemannianCoordinateMetric a z v v := by
  rw [riemannianCoordinateMetric_apply,real_inner_self_pos]
  have hbase : (extChartAt 𝓘(ℝ,E) a).symm z ∈
      (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) a).map_target hz
  exact fun hzero => hv (((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).continuousLinearEquivAt ℝ _ hbase).symm.injective
        (by simpa only [Trivialization.symm_continuousLinearEquivAt_eq,map_zero] using hzero))

variable [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma contDiffOn_riemannianCoordinateMetric (a : M) :
    ContDiffOn ℝ ∞ (riemannianCoordinateMetric a) (extChartAt 𝓘(ℝ,E) a).target := by
  let T := fun x : M => TangentSpace 𝓘(ℝ,E) x
  obtain ⟨b,hb,hinner⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
    (IB := 𝓘(ℝ,E)) (n := ∞) (F := E) (E := T)
  let e := trivializationAt E T a
  let eB := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) (fun x => T x →L[ℝ] T x →L[ℝ] ℝ) a
  let c : M → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    inCoordinates E T (E →L[ℝ] ℝ) (fun x => T x →L[ℝ] ℝ) a x a x (b x)
  have hc : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ c e.baseSet := by
    intro x hx
    have hxB : x ∈ eB.baseSet := by
      change x ∈ e.baseSet ∩ (e.baseSet ∩ univ)
      exact ⟨hx,hx,mem_univ x⟩
    have hh := (eB.contMDiffAt_section_iff hxB).mp (hb x)
    exact hh.contMDiffWithinAt
  have hmaps : MapsTo (extChartAt 𝓘(ℝ,E) a).symm
      (extChartAt 𝓘(ℝ,E) a).target e.baseSet := by
    intro z hz
    change (extChartAt 𝓘(ℝ,E) a).symm z ∈ (chartAt E a).source
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) a).map_target hz
  have hs := hc.comp (contMDiffOn_extChartAt_symm a) hmaps
  apply (contMDiffOn_iff_contDiffOn.mp hs).congr
  intro z hz
  ext u v
  change riemannianCoordinateMetric a z u v = c ((extChartAt 𝓘(ℝ,E) a).symm z) u v
  simp only [c]
  rw [inCoordinates_apply_eq₂ (hmaps hz) (hmaps hz) (mem_univ _)]
  rw [riemannianCoordinateMetric_apply,hinner]
  simp only [Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization,
    LinearMap.id_coe,id_eq]
  change b _ (e.symmL ℝ _ u) (e.symmL ℝ _ v) = b _ (e.symm _ u) (e.symm _ v)
  rw [Trivialization.symmL_apply e (hmaps hz),Trivialization.symmL_apply e (hmaps hz)]

end WeakMTWTransport

end

end OAI
