import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma exists_smooth_inverse_data :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      ∃ H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht,
        (∀ f, smoothL2 A J α hs ht true (H f).val =
          (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f, IsClosed (H f).val.val) ∧
        (∀ f, antiToEnergy A J α hs ht (Gs f) = G (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
            weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫) := by
  classical
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  let j := (harmonicAnti A J α hs ht).starProjection.toLinearMap.comp i
  have hH : ∀ f, ∃ h : antiPre A J α hs ht, i h = j f := by
    intro f
    obtain ⟨h,hh,-⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    exact ⟨h,hh⟩
  let H := InjectiveLinearLift.lift i hi j hH
  have hHspec (f) : i (H f) = j f := InjectiveLinearLift.lift_spec i hi j hH f
  have hHclosed (f) : IsClosed (H f).val.val := by
    obtain ⟨h,hh,hc⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    have he : H f = h := hi ((hHspec f).trans hh.symm)
    rw [he]
    exact coclosed_antiInvariant_closed J α ht h.val.property h.property hc
  obtain ⟨-,G,hG,-,-,hGs⟩ := geometric_smooth_inverse A J α hs ht D hD
  have hanti : Function.Injective (antiToEnergy A J α hs ht) := by
    intro a b hab
    apply hi
    exact congrArg (energyInclusion A J α hs ht) hab
  let Gs := InjectiveLinearLift.lift (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs
  have hGspec (f) : antiToEnergy A J α hs ht (Gs f) = G (i f) :=
    InjectiveLinearLift.lift_spec (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs f
  refine ⟨G,H,Gs,hHspec,hHclosed,hGspec,fun f v => ?_⟩
  rw [hGspec,hG]
  change ⟪i f - j f,energyInclusion A J α hs ht v⟫ =
    ⟪i (f-H f),energyInclusion A J α hs ht v⟫
  rw [map_sub,hHspec]

end TamingCompatibility.GeometricHilbert

end

end OAI
