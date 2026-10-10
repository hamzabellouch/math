import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFredholm
import OAI.Geometry.TamingCompatibility.Elliptic.GlobalSmoothRegularity

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma harmonicAnti_smooth (f : L2 A J α hs ht true) (hf : f ∈ harmonicAnti A J α hs ht) :
    ∃ b : antiPre A J α hs ht, smoothL2 A J α hs ht true b.val = f ∧
      codifferential J α ht b.val.val = 0 := by
  obtain ⟨u,hu,hd⟩ := (mem_harmonicAnti A J α hs ht f).mp hf
  obtain ⟨b,hb⟩ := weak_kernel_smooth A J α hs ht D hD u hd
  refine ⟨b,?_,?_⟩
  · rw [← hb] at hu
    exact hu
  · rw [← hb] at hd
    change smoothL2 A J α hs ht false (antiDelta A J α hs ht b) = 0 at hd
    have he := (smoothL2 A J α hs ht false).injective (hd.trans (map_zero _).symm)
    exact congrArg Subtype.val he

include hD in

theorem geometric_smooth_inverse :
    FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
      ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
        (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
          ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
        (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
        (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) ∧
        (∀ f : antiPre A J α hs ht, ∃ b : antiPre A J α hs ht,
          antiToEnergy A J α hs ht b = G (smoothL2 A J α hs ht true f.val)) := by
  obtain ⟨hfin,G,hG,horth,hGzero⟩ := geometric_weak_inverse A J α hs ht D hD
  refine ⟨hfin,G,hG,horth,hGzero,fun f => ?_⟩
  obtain ⟨h,hh,-⟩ := harmonicAnti_smooth A J α hs ht D hD
    ((harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    ((harmonicAnti A J α hs ht).starProjection_apply_mem _)
  apply weak_solution_smooth A J α hs ht D hD (f-h)
  intro v
  rw [hG,← hh]
  change _ = ⟪smoothL2 A J α hs ht true (f.val-h.val),energyInclusion A J α hs ht v⟫
  rw [map_sub]

end TamingCompatibility.GeometricHilbert

end

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiRdd (a : antiPre A J α hs ht) : antiPre A J α hs ht :=
  ⟨⟨rdd J α ht a.val.val,rdd_smooth J α hs ht a.val.property⟩,
    antiInvariantPart_idempotent J _⟩

lemma antiRdd_green (a b : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true (antiRdd A J α hs ht a).val,smoothL2 A J α hs ht true b.val⟫ =
    ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),
      weakDelta A J α hs ht (antiToEnergy A J α hs ht b)⟫ := by
  change ⟪smoothL2 A J α hs ht true (antiRdd A J α hs ht a).val,smoothL2 A J α hs ht true b.val⟫ =
    ⟪smoothL2 A J α hs ht false (antiDelta A J α hs ht a),smoothL2 A J α hs ht false (antiDelta A J α hs ht b)⟫
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht false).inner_map_map,
    preL2_inner,preL2_inner]
  exact rdd_green A J α hs ht a.val.property b.val.property b.property

lemma strong_weak_equation (a f : antiPre A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht,
      ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    rdd J α ht a.val.val = f.val.val := by
  have he : antiRdd A J α hs ht a = f := by
    apply ext_inner_right ℝ
    intro b
    change ⟪(antiRdd A J α hs ht a).val,b.val⟫ = ⟪f.val,b.val⟫
    rw [← (smoothL2 A J α hs ht true).inner_map_map,
      ← (smoothL2 A J α hs ht true).inner_map_map,antiRdd_green]
    exact heq (antiToEnergy A J α hs ht b)
  exact congrArg (fun b : antiPre A J α hs ht => b.val.val) he

end TamingCompatibility.GeometricHilbert

end

noncomputable section
namespace InjectiveLinearLift
variable {R E F G : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
  [AddCommMonoid G] [Module R E] [Module R F] [Module R G]

def lift (i : E →ₗ[R] F) (hi : Function.Injective i) (j : G →ₗ[R] F)
    (h : ∀ g, ∃ e, i e = j g) : G →ₗ[R] E where
  toFun g := Classical.choose (h g)
  map_add' a b := hi (by rw [Classical.choose_spec (h (a+b)),map_add,map_add,
    Classical.choose_spec (h a),Classical.choose_spec (h b)])
  map_smul' r a := hi (by rw [Classical.choose_spec (h (r • a)),map_smul,map_smul,
    Classical.choose_spec (h a)]; rfl)

lemma lift_spec (i : E →ₗ[R] F) (hi : Function.Injective i) (j : G →ₗ[R] F)
    (h : ∀ g, ∃ e, i e = j g) (g : G) : i (lift i hi j h g) = j g :=
  Classical.choose_spec (h g)
end InjectiveLinearLift


namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem exists_smooth_closed_lift :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ a, IsClosed (B a).val) ∧ (∀ a, antiInvariantPart J (B a).val = a.val.val) := by
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
  have hstrong (f) : rdd J α ht (Gs f).val.val = (f-H f).val.val := by
    apply strong_weak_equation A J α hs ht
    intro v
    rw [hGspec,hG]
    change ⟪i f - j f,energyInclusion A J α hs ht v⟫ =
      ⟪i (f-H f),energyInclusion A J α hs ht v⟫
    rw [map_sub,hHspec]
  let B₁ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (d.comp (antiDelta A J α hs ht)).comp Gs
  let B₂ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (antiPre A J α hs ht).subtype.comp H
  let B := B₁ + B₂
  refine ⟨B,fun f => ?_,fun f => ?_⟩
  · change IsClosed ((B₁ f).val + (B₂ f).val)
    exact IsClosed.add ((codifferential_smooth J α hs ht (Gs f).val.property).closed_exteriorDerivative)
      (hHclosed f) (Smooth.exteriorDerivative (codifferential_smooth J α hs ht (Gs f).val.property)) (H f).val.property
  · change antiInvariantPart J ((B₁ f).val + (B₂ f).val) = f.val.val
    rw [antiInvariantPart_add]
    change rdd J α ht (Gs f).val.val + antiInvariantPart J (H f).val.val = f.val.val
    rw [(H f).property]
    have he := congrArg (fun a : antiPre A J α hs ht => a.val.val) (sub_add_cancel f (H f))
    rw [hstrong]
    exact he

end TamingCompatibility.GeometricHilbert

end

end OAI
