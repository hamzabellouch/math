import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.ReesCharts

namespace OAI

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry

def lineBundleOfCover {X : Scheme} (M : X.Modules) (C : X.OpenCover)
    (h : ∀ i, Nonempty (M.restrict (C.f i) ≅ IdealModule.unit (C.X i))) : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    refine ⟨(C.f (C.idx x)).opensRange, C.covers x, ?_⟩
    exact ⟨IdealModule.frameOnRange M (C.f (C.idx x)) (h (C.idx x)).some⟩

def idealLineBundle {X : Scheme} (I : X.IdealSheafData) (C : X.AffineOpenCover)
    (r : ∀ i, Γ(Spec (C.X i), ⊤))
    (h : ∀ i, (I.comap (C.f i)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r i})
    (hr : ∀ i, IsLeftRegular (r i)) : LineBundle X :=
  lineBundleOfCover (IdealModule.closedModule I) C.openCover
    (fun i => by
      let : IsOpenImmersion (C.f i) := C.map_prop i
      exact IdealModule.frame_restriction I (C.f i) (r i) (h i) (hr i))

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def exceptionalIdeal : (affineBlowup I).IdealSheafData :=
  (IdealPullback.specIdeal I).comap (projection I)

def chartEquation (a : I) : Γ(Spec ((chartCover I).X a), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv (chartBase I a a.val)

lemma exceptional_chart (a : I) :
    ((exceptionalIdeal I).comap ((chartCover I).f a)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {chartEquation I a} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartCover_projection]
  change ((IdealPullback.specIdeal I).comap
      (Spec.map (CommRingCat.ofHom (chartBase I a)))).ideal
      ⟨(⊤ : (Spec (CommRingCat.of (chart I a))).Opens), isAffineOpen_top _⟩ =
    Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv (chartBase I a a.val)}
  rw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, map_ideal_principal,
    Ideal.map_span, Set.image_singleton]

lemma chartEquation_regular (a : I) : IsLeftRegular (chartEquation I a) := by
  apply IdealModule.regular_map_flat _ _ (chart_generator_regular I a).left
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv)

end

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

def exceptionalLineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ IdealModule.unit (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance exceptionalInclusion_mono : Mono (exceptionalInclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))

end

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma exceptional_presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) := by
  refine ⟨exceptionalInclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem exceptional_invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I)
    (projection I) :=
  ⟨exceptionalLineBundle I, exceptionalInclusion I, exceptional_presents I⟩

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.BlowupLift
noncomputable section
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsLeftRegular r)

def coefficient (a : I) : S :=
  Classical.choose ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))

lemma mul_coefficient (a : I) : r * coefficient I f r hI a = f a.val := by
  exact (Classical.choose_spec ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))).symm

include hr in

lemma coefficients_span : Ideal.span (Set.range (coefficient I f r hI)) = ⊤ := by
  let K : Ideal S := Ideal.span (Set.range (coefficient I f r hI))
  have hmap : I.map f ≤ Submodule.map (LinearMap.mulLeft S r) K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Submodule.map (LinearMap.mulLeft S r) K
    exact ⟨coefficient I f r hI ⟨a, ha⟩,
      Ideal.subset_span (Set.mem_range_self _), mul_coefficient I f r hI ⟨a, ha⟩⟩
  have hmem : r ∈ Submodule.map (LinearMap.mulLeft S r) K := by
    apply hmap
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨s, hs, hrs⟩ := hmem
  have hs1 : s = 1 := hr (by simpa using hrs)
  refine Ideal.eq_top_of_isUnit_mem (I := K) ?_ isUnit_one
  exact hs1 ▸ hs

end
end MaximalSeshadri.BlowupLift


end

end OAI
