import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Coordinates

namespace OAI

noncomputable section

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance smoothDistanceNormedSpace : NormedSpace ℝ E :=
  InnerProductSpace.toNormedSpace
local instance smoothDistanceNormedAddCommGroupEndomorphism :
    NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceEndomorphism :
    NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance smoothDistanceNormedAddCommGroupDual :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceDual :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smoothDistanceNormedAddCommGroupBilinear :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceBilinear :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

lemma derivative_pullback_metric
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : DifferentiableAt ℝ φ x) (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (w u v : E) :
    fderiv ℝ g x w u v =
      fderiv ℝ h (φ x) (fderiv ℝ φ x w) (fderiv ℝ φ x u) (fderiv ℝ φ x v) +
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x w u) (fderiv ℝ φ x v) +
      h (φ x) (fderiv ℝ φ x u) (fderiv ℝ (fderiv ℝ φ) x w v) := by
  have hleft := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  have hright := ((hh.hasFDerivAt.comp x hφ.hasFDerivAt).clm_apply
    (hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const u x))).clm_apply
    (hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have heq : (fun y => g y u v) =ᶠ[𝓝 x]
      (fun y => h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v)) := by
    filter_upwards [hmetric] with y hy; exact hy u v
  have he := congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc,add_comm,add_left_comm] using he

lemma christoffel_pushforward_pairing
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) (u v w : E) :
    h (φ x) (fderiv ℝ φ x (coordinateChristoffel g x u v)) (fderiv ℝ φ x w) =
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v))
        (fderiv ℝ φ x w) := by
  have hpd := hφ.differentiableAt (by simp)
  have hD := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp := derivative_pullback_metric hg hh hpd hD hmetric
  have hm := hmetric.self_of_nhds
  have hb : ∀ u v, fderiv ℝ (fderiv ℝ φ) x u v = fderiv ℝ (fderiv ℝ φ) x v u := by
    intro u v
    exact (hφ.isSymmSndFDerivAt (by simp)).eq u v
  have h1 := coordinateChristoffel_metric g x u v w hgi
  have h2 := coordinateChristoffel_metric h (φ x) (fderiv ℝ φ x u)
    (fderiv ℝ φ x v) (fderiv ℝ φ x w) hhi
  rw [hm,hp u v w,hp v u w,hp w u v] at h1
  rw [hb v u,hb w u,hb w v] at h1
  rw [hhs (fderiv ℝ φ x v) _,hhs (fderiv ℝ φ x u) _] at h1
  simp only [map_add,add_apply]
  linarith

lemma christoffel_pushforward
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x) (hφs : Function.Surjective (fderiv ℝ φ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) (u v : E) :
    fderiv ℝ φ x (coordinateChristoffel g x u v) =
      fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  have heq : h (φ x) (fderiv ℝ φ x (coordinateChristoffel g x u v)) =
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v)) := by
    ext w
    obtain ⟨z,rfl⟩ := hφs w
    exact christoffel_pushforward_pairing hg hh hφ hmetric hgi hhi hhs u v z
  rcases hhi with ⟨A,hA⟩
  apply A.injective
  change A.toContinuousLinearMap _ = A.toContinuousLinearMap _
  rw [hA]
  exact heq
end WeakMTWTransport

end

end OAI
