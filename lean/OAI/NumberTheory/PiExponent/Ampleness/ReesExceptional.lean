import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal
import OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
open Polynomial DirectSum AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma generators_adjoin : Algebra.adjoin R (Set.range (generator I)) = ⊤ := by
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin]
  have hs : (reesAlgebra I).val '' Set.range (generator I) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    ext p
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨generator I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [hs, adjoin_monomial_eq_reesAlgebra]
  rw [Algebra.map_top, Subalgebra.range_val]

lemma generators_adjoin_zero :
    Algebra.adjoin (piece I 0) (Set.range (generator I)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  have hh : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range (generator I))).algebraMap_mem (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

lemma iSup_generator_basicOpen :
    ⨆ a : I, Proj.basicOpen (piece I) (generator I a) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (generator I)
    (fun a => ⟨1, generator_mem I a⟩) (generators_adjoin_zero I)

def chartCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (chart I a)
  f a := Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)
  map_prop a := inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)))
  idx x := (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (m := 1) (piece I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose_spec

lemma chartCover_projection (a : I) :
    (chartCover I).f a ≫ projection I = Spec.map (CommRingCat.ofHom (chartBase I a)) := by
  change Proj.awayι (m := 1) (piece I) (generator I a) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end PiExponentSeshadri.ReesGrading
namespace PiExponentSeshadri.Geometry
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

end PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.ReesGrading

section
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
  erw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, map_ideal_principal,
    Ideal.map_span, Set.image_singleton]
  rfl

lemma chartEquation_regular (a : I) : IsLeftRegular (chartEquation I a) := by
  apply IdealModule.regular_map_flat _ _ (chart_generator_regular I a).left
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv)

end

open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

def exceptionalLineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ IdealModule.unit (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance exceptionalInclusion_mono : Mono (exceptionalInclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))



lemma exceptional_presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) := by
  refine ⟨exceptionalInclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem exceptional_invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I)
    (projection I) :=
  ⟨exceptionalLineBundle I, exceptionalInclusion I, exceptional_presents I⟩

end PiExponentSeshadri.ReesGrading

end

end OAI
