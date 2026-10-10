import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import OAI.Geometry.NodalSets.Elliptic.PositiveBilinearBound
import OAI.Geometry.NodalSets.Elliptic.SmoothBilinearPullback

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

local instance (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

omit [FiniteDimensional ℝ E] in
lemma smooth_ambient_derivative (f : M → W) (hf : ContMDiff I 𝓘(ℝ,W) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ,E →L[ℝ] W)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] W)
        (E := fun x ↦ TangentSpace I x →L[ℝ] Bundle.Trivial M W x)
        x (mfderiv I 𝓘(ℝ,W) f x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have hd := (hf x).mfderiv_const (m := ∞) (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, inCoordinates, ContinuousLinearMap.one_def]
  rfl

def immersionMetric (f : M → W) (hf : ContMDiff I 𝓘(ℝ,W) ∞ f)
    (hi : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ,W) f x))
    (B : M → W →L[ℝ] W →L[ℝ] ℝ)
    (hB : ContMDiff I 𝓘(ℝ,W →L[ℝ] W →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) where
  inner x := bilinearPullback (B x) (mfderiv I 𝓘(ℝ,W) f x)
  symm x _ _ := hs x _ _
  pos x _ hv := hp x _ (fun he ↦ hv (hi x (he.trans (map_zero _).symm)))
  isVonNBounded x := positive_bilinear_bounded _
    (fun _ hv ↦ hp x _ (fun he ↦ hv (hi x (he.trans (map_zero _).symm))))
  contMDiff := @smooth_bilinear_pullback E _ _ H _ I M _ _ E _ _
    (fun x : M ↦ TangentSpace I x) _ _ _
    (TangentSpace.fiberBundle (I := I) (M := M))
    (TangentSpace.vectorBundle (I := I) (M := M)) W _ _ B
    (fun x ↦ mfderiv I 𝓘(ℝ,W) f x) hB (smooth_ambient_derivative f hf)

lemma immersionMetric_inner (f : M → W) (hf : ContMDiff I 𝓘(ℝ,W) ∞ f)
    (hi : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ,W) f x))
    (B : M → W →L[ℝ] W →L[ℝ] ℝ)
    (hB : ContMDiff I 𝓘(ℝ,W →L[ℝ] W →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v) (x : M) (v w : TangentSpace I x) :
    (immersionMetric f hf hi B hB hs hp).inner x v w =
      B x (mfderiv I 𝓘(ℝ,W) f x v) (mfderiv I 𝓘(ℝ,W) f x w) := rfl

end
end Yau.Geometry

end OAI
