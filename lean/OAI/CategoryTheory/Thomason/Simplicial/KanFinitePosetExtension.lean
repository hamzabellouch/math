import OAI.CategoryTheory.Thomason.Chains.NerveFaceChains
import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Gray.SubdivisionPrismNaturality
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSupportInclusion
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionImageLattice
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionKan
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialApproximation
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionWeakLifting

namespace OAI

section

/-! # Subdivision descent with a homotopy over the prescribed base

The greatest-vertex prism is stationary after projection.  Consequently
the descended map and its comparison homotopy both respect the given
base map exactly.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

theorem exists_subdivision_stationary_descent_over_kan {K E B : SSet.{0}}
    [SSet.KanComplex B] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hK : SSet.anodyneExtensions (canonicalExtension.app K))
    (hSd : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj K)))
    (a : SSet.sd.obj K ⟶ E) (b : K ⟶ B)
    (hab : a ≫ p = lastVertex.app K ≫ b) :
    ∃ (g : K ⟶ E) (H : SSet.Homotopy (lastVertex.app K ≫ g) a),
      g ≫ p = b ∧ H.h ≫ p = fst (SSet.sd.obj K) Δ[1] ≫ lastVertex.app K ≫ b := by
  let t : B ⟶ ⊤_ SSet.{0} := terminal.from B
  have ht : J.rlp t := (fibration_iff t).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app K) t := hK t ht
  let sqB : CommSq b (canonicalExtension.app K) t
      (terminal.from (SSet.ex.obj K)) := ⟨Subsingleton.elim _ _⟩
  let q : SSet.ex.obj (SSet.sd.obj K) ⟶ B :=
    SSet.ex.map (lastVertex.app K) ≫ sqB.lift
  have hp : J.rlp p := (fibration_iff p).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app (SSet.sd.obj K)) p := hSd p hp
  let sq : CommSq a (canonicalExtension.app (SSet.sd.obj K)) p q := ⟨by
    rw [hab]
    change lastVertex.app K ≫ b = canonicalExtension.app (SSet.sd.obj K) ≫
      (SSet.ex.map (lastVertex.app K) ≫ sqB.lift)
    rw [← Category.assoc, ← canonicalExtension.naturality, Category.assoc]
    change lastVertex.app K ≫ b = lastVertex.app K ≫
      (canonicalExtension.app K ≫ sqB.lift)
    rw [sqB.fac_left]⟩
  let g : K ⟶ E := SSet.sdExAdjunction.unit.app K ≫ sq.lift
  have hgp : g ≫ p = b := by
    change (SSet.sdExAdjunction.unit.app K ≫ sq.lift) ≫ p = b
    rw [Category.assoc, sq.fac_right]
    change SSet.sdExAdjunction.unit.app K ≫
      (SSet.ex.map (lastVertex.app K) ≫ sqB.lift) = b
    rw [← Category.assoc,
      subdivision_unit_extension_lastVertex, sqB.fac_left]
  let H₀ := postcomposeSimplicialHomotopy (subdivisionUnitHomotopy K) sq.lift
  let H : SSet.Homotopy (lastVertex.app K ≫ g) a :=
    { h := H₀.h
      h₀ := H₀.h₀.trans (Category.assoc _ _ _)
      h₁ := H₀.h₁.trans sq.fac_left
      rel := H₀.rel }
  refine ⟨g, H, hgp, ?_⟩
  change ((subdivisionUnitHomotopy K).h ≫ sq.lift) ≫ p = _
  rw [Category.assoc, sq.fac_right]
  change (subdivisionUnitHomotopy K).h ≫
    (SSet.ex.map (lastVertex.app K) ≫ sqB.lift) = _
  rw [← Category.assoc, subdivisionUnitHomotopy_stationary,
    Category.assoc, Category.assoc, sqB.fac_left]

theorem exists_finitePoset_subdivision_stationary_descent_over_kan
    (P : Type) [PartialOrder P] [Finite P] {E B : SSet.{0}}
    [SSet.KanComplex B] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (a : SSet.sd.obj (nerve P) ⟶ E) (b : nerve P ⟶ B)
    (hab : a ≫ p = lastVertex.app (nerve P) ≫ b) :
    ∃ (g : nerve P ⟶ E) (H : SSet.Homotopy (lastVertex.app (nerve P) ≫ g) a),
      g ≫ p = b ∧ H.h ≫ p = fst (SSet.sd.obj (nerve P)) Δ[1] ≫
        lastVertex.app (nerve P) ≫ b :=
  exists_subdivision_stationary_descent_over_kan p (canonicalExtension_finitePoset_anodyne P)
    (canonicalExtension_subdivision_finitePoset_anodyne P) a b hab

end

end Thomason.Construction

end

section

/-! # Subdivision descent fixing a prescribed subcomplex

The extension on the prescribed source is chosen through its original
canonical extension.  Relative anodyne lifting then preserves both that
extension and the original subdivided map.  Naturality and stationarity
make the resulting comparison homotopy constant on the prescribed source.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

theorem exists_subdivision_domain_relative_descent {A B X : SSet.{0}}
    [SSet.KanComplex X] (i : A ⟶ B) [Mono i]
    (hA : SSet.anodyneExtensions (canonicalExtension.app A))
    (hSdA : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj A)))
    (hSdB : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj B)))
    (a : A ⟶ X) (f : SSet.sd.obj B ⟶ X)
    (hi : SSet.sd.map i ≫ f = lastVertex.app A ≫ a) :
    ∃ (g : B ⟶ X) (H : SSet.Homotopy (lastVertex.app B ≫ g) f),
      i ≫ g = a ∧ (SSet.sd.map i ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj A) Δ[1] ≫ lastVertex.app A ≫ a := by
  let t : X ⟶ ⊤_ SSet.{0} := terminal.from X
  have ht : J.rlp t := (fibration_iff t).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app A) t := hA t ht
  let sqA : CommSq a (canonicalExtension.app A) t
      (terminal.from (SSet.ex.obj A)) := ⟨Subsingleton.elim _ _⟩
  let q : SSet.ex.obj (SSet.sd.obj A) ⟶ X :=
    SSet.ex.map (lastVertex.app A) ≫ sqA.lift
  have hq : SSet.sd.map i ≫ f = canonicalExtension.app (SSet.sd.obj A) ≫ q := by
    rw [hi]
    change lastVertex.app A ≫ a = canonicalExtension.app (SSet.sd.obj A) ≫
      (SSet.ex.map (lastVertex.app A) ≫ sqA.lift)
    rw [← Category.assoc, ← canonicalExtension.naturality, Category.assoc]
    change lastVertex.app A ≫ a = lastVertex.app A ≫
      (canonicalExtension.app A ≫ sqA.lift)
    rw [sqA.fac_left]
  let d : pushout (SSet.sd.map i) (canonicalExtension.app (SSet.sd.obj A)) ⟶ X :=
    pushout.desc f q hq
  have := subdivision_map_mono i
  have hrel := relativeCanonicalExtension_anodyne (SSet.sd.map i) hSdA hSdB
  let : HasLiftingProperty (relativeCanonicalExtension (SSet.sd.map i)) t := hrel t ht
  let sqB : CommSq d (relativeCanonicalExtension (SSet.sd.map i)) t
      (terminal.from (SSet.ex.obj (SSet.sd.obj B))) := ⟨Subsingleton.elim _ _⟩
  have hr₀ : canonicalExtension.app (SSet.sd.obj B) ≫ sqB.lift = f := by
    rw [← relativeCanonicalExtension_inl (SSet.sd.map i), Category.assoc, sqB.fac_left]
    exact pushout.inl_desc f q hq
  have hr₁ : SSet.ex.map (SSet.sd.map i) ≫ sqB.lift = q := by
    rw [← relativeCanonicalExtension_inr (SSet.sd.map i), Category.assoc, sqB.fac_left]
    exact pushout.inr_desc f q hq
  let g : B ⟶ X := SSet.sdExAdjunction.unit.app B ≫ sqB.lift
  have hgi : i ≫ g = a := by
    have hn : i ≫ SSet.sdExAdjunction.unit.app B =
        SSet.sdExAdjunction.unit.app A ≫ SSet.ex.map (SSet.sd.map i) :=
      SSet.sdExAdjunction.unit.naturality i
    change i ≫ (SSet.sdExAdjunction.unit.app B ≫ sqB.lift) = a
    rw [← Category.assoc, hn, Category.assoc, hr₁]
    change SSet.sdExAdjunction.unit.app A ≫
      (SSet.ex.map (lastVertex.app A) ≫ sqA.lift) = a
    rw [← Category.assoc, subdivision_unit_extension_lastVertex, sqA.fac_left]
  let H₀ := postcomposeSimplicialHomotopy (subdivisionUnitHomotopy B) sqB.lift
  let H : SSet.Homotopy (lastVertex.app B ≫ g) f :=
    { h := H₀.h
      h₀ := H₀.h₀.trans (Category.assoc _ _ _)
      h₁ := H₀.h₁.trans hr₀
      rel := H₀.rel }
  refine ⟨g, H, hgi, ?_⟩
  change (SSet.sd.map i ▷ Δ[1]) ≫ ((subdivisionUnitHomotopy B).h ≫ sqB.lift) = _
  rw [← Category.assoc, subdivisionUnitHomotopy_naturality, Category.assoc, hr₁]
  change (subdivisionUnitHomotopy A).h ≫
    (SSet.ex.map (lastVertex.app A) ≫ sqA.lift) = _
  rw [← Category.assoc, subdivisionUnitHomotopy_stationary,
    Category.assoc, Category.assoc, sqA.fac_left]

theorem exists_finitePoset_subdivision_domain_relative_descent
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    {X : SSet.{0}} [SSet.KanComplex X] (i : nerve P ⟶ nerve Q) [Mono i]
    (a : nerve P ⟶ X) (f : SSet.sd.obj (nerve Q) ⟶ X)
    (hi : SSet.sd.map i ≫ f = lastVertex.app (nerve P) ≫ a) :
    ∃ (g : nerve Q ⟶ X) (H : SSet.Homotopy (lastVertex.app (nerve Q) ≫ g) f),
      i ≫ g = a ∧ (SSet.sd.map i ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj (nerve P)) Δ[1] ≫ lastVertex.app (nerve P) ≫ a :=
  exists_subdivision_domain_relative_descent i (canonicalExtension_finitePoset_anodyne P)
    (canonicalExtension_subdivision_finitePoset_anodyne P)
    (canonicalExtension_subdivision_finitePoset_anodyne Q) a f hi

theorem canonicalExtension_subdivision_twice_subcomplex_anodyne {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.anodyneExtensions
      (canonicalExtension.app (SSet.sd.obj (SSet.sd.obj A.toSSet))) := by
  rw [← faceUnion_subcomplexFaceFamily A]
  have := finite_nonemptyFiniteChains (ULift.{0} (Fin (n+1)))
  exact canonicalExtension_anodyne_of_iso
    (SSet.sd.mapIso (faceUnionSubdivisionIso (subcomplexFaceFamily A)))
    (canonicalExtension_subdivision_finitePoset_anodyne
      (faceFamilyVertices (subcomplexFaceFamily A)))

/-- A second subdivision of finite simplex subcomplexes can be removed
while fixing the entire once-subdivided prescribed source. -/
theorem exists_twice_subdivision_domain_relative_descent {m n : ℕ}
    (A : (Δ[m] : SSet.{0}).Subcomplex) (B : (Δ[n] : SSet.{0}).Subcomplex)
    {X : SSet.{0}} [SSet.KanComplex X] (i : A.toSSet ⟶ B.toSSet) [Mono i]
    (a : SSet.sd.obj A.toSSet ⟶ X) (f : SSet.sd.obj (SSet.sd.obj B.toSSet) ⟶ X)
    (hi : SSet.sd.map (SSet.sd.map i) ≫ f = lastVertex.app (SSet.sd.obj A.toSSet) ≫ a) :
    ∃ (g : SSet.sd.obj B.toSSet ⟶ X)
      (H : SSet.Homotopy (lastVertex.app (SSet.sd.obj B.toSSet) ≫ g) f),
      SSet.sd.map i ≫ g = a ∧ (SSet.sd.map (SSet.sd.map i) ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj (SSet.sd.obj A.toSSet)) Δ[1] ≫
          lastVertex.app (SSet.sd.obj A.toSSet) ≫ a := by
  have := subdivision_map_mono i
  exact exists_subdivision_domain_relative_descent (SSet.sd.map i)
    (canonicalExtension_subdivision_subcomplex_anodyne A)
    (canonicalExtension_subdivision_twice_subcomplex_anodyne A)
    (canonicalExtension_subdivision_twice_subcomplex_anodyne B) a f hi

end

end Thomason.Construction

end

section

/-! # Subdivision descent fixing the entire original boundary -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- A subdivision of a simplex subcomplex can be removed while preserving
any prescribed simplex subcomplex and its entire constant homotopy. -/
theorem exists_simplexSubcomplex_subdivision_relative_descent {m n : ℕ}
    (A : (Δ[m] : SSet.{0}).Subcomplex) (B : (Δ[n] : SSet.{0}).Subcomplex)
    {X : SSet.{0}} [SSet.KanComplex X] (i : A.toSSet ⟶ B.toSSet) [Mono i]
    (a : A.toSSet ⟶ X) (f : SSet.sd.obj B.toSSet ⟶ X)
    (hi : SSet.sd.map i ≫ f = lastVertex.app A.toSSet ≫ a) :
    ∃ (g : B.toSSet ⟶ X) (H : SSet.Homotopy (lastVertex.app B.toSSet ≫ g) f),
      i ≫ g = a ∧ (SSet.sd.map i ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj A.toSSet) Δ[1] ≫ lastVertex.app A.toSSet ≫ a :=
  exists_subdivision_domain_relative_descent i
    (canonicalExtension_simplexSubcomplex_anodyne A)
    (canonicalExtension_subdivision_subcomplex_anodyne A)
    (canonicalExtension_subdivision_subcomplex_anodyne B) a f hi

theorem exists_boundary_subdivision_relative_descent (n : ℕ)
    {X : SSet.{0}} [SSet.KanComplex X]
    (a : (SSet.boundary.{0} n).toSSet ⟶ X)
    (f : SSet.sd.obj (Δ[n] : SSet.{0}) ⟶ X)
    (hi : SSet.sd.map (SSet.boundary.{0} n).ι ≫ f =
      lastVertex.app (SSet.boundary.{0} n).toSSet ≫ a) :
    ∃ (g : (Δ[n] : SSet.{0}) ⟶ X)
      (H : SSet.Homotopy (lastVertex.app (Δ[n] : SSet.{0}) ≫ g) f),
      (SSet.boundary.{0} n).ι ≫ g = a ∧
        (SSet.sd.map (SSet.boundary.{0} n).ι ▷ Δ[1]) ≫ H.h =
          fst (SSet.sd.obj (SSet.boundary.{0} n).toSSet) Δ[1] ≫
            lastVertex.app (SSet.boundary.{0} n).toSSet ≫ a :=
  exists_subdivision_domain_relative_descent (SSet.boundary.{0} n).ι
    (canonicalExtension_boundary_anodyne n)
    (canonicalExtension_subdivision_boundary_anodyne n)
    (canonicalExtension_subdivision_standard_anodyne n) a f hi

end

end Thomason.Construction

end

section

/-! # Subdivision descent fixing both the source and the base

The relative extension lift fixes the given source map.  Choosing it over
the extended base map also makes the comparison homotopy stationary over
that base.  All four extension premises hold for simplex subcomplexes.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

theorem exists_subdivision_relative_base_descent {A B E Z : SSet.{0}}
    [SSet.KanComplex Z] (i : A ⟶ B) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hA : SSet.anodyneExtensions (canonicalExtension.app A))
    (hB : SSet.anodyneExtensions (canonicalExtension.app B))
    (hSdA : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj A)))
    (hSdB : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj B)))
    (a : A ⟶ E) (f : SSet.sd.obj B ⟶ E) (b : B ⟶ Z)
    (ha : a ≫ p = i ≫ b)
    (hf : f ≫ p = lastVertex.app B ≫ b)
    (hi : SSet.sd.map i ≫ f = lastVertex.app A ≫ a) :
    ∃ (g : B ⟶ E) (H : SSet.Homotopy (lastVertex.app B ≫ g) f),
      i ≫ g = a ∧ g ≫ p = b ∧
      (SSet.sd.map i ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj A) Δ[1] ≫ lastVertex.app A ≫ a ∧
      H.h ≫ p = fst (SSet.sd.obj B) Δ[1] ≫ lastVertex.app B ≫ b := by
  let t : Z ⟶ ⊤_ SSet.{0} := terminal.from Z
  have ht : J.rlp t := (fibration_iff t).mp inferInstance
  have hp : J.rlp p := (fibration_iff p).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app B) t := hB t ht
  let sqZ : CommSq b (canonicalExtension.app B) t
      (terminal.from (SSet.ex.obj B)) := ⟨Subsingleton.elim _ _⟩
  let : HasLiftingProperty (canonicalExtension.app A) p := hA p hp
  let sqA : CommSq a (canonicalExtension.app A) p (SSet.ex.map i ≫ sqZ.lift) := ⟨by
    rw [ha, ← Category.assoc, ← canonicalExtension.naturality, Category.assoc]
    change i ≫ b = i ≫ (canonicalExtension.app B ≫ sqZ.lift)
    rw [sqZ.fac_left]⟩
  let qA : SSet.ex.obj (SSet.sd.obj A) ⟶ E :=
    SSet.ex.map (lastVertex.app A) ≫ sqA.lift
  have hq : SSet.sd.map i ≫ f = canonicalExtension.app (SSet.sd.obj A) ≫ qA := by
    rw [hi]
    change lastVertex.app A ≫ a = canonicalExtension.app (SSet.sd.obj A) ≫
      (SSet.ex.map (lastVertex.app A) ≫ sqA.lift)
    rw [← Category.assoc, ← canonicalExtension.naturality, Category.assoc]
    change lastVertex.app A ≫ a = lastVertex.app A ≫
      (canonicalExtension.app A ≫ sqA.lift)
    rw [sqA.fac_left]
  let d : pushout (SSet.sd.map i) (canonicalExtension.app (SSet.sd.obj A)) ⟶ E :=
    pushout.desc f qA hq
  let qB : SSet.ex.obj (SSet.sd.obj B) ⟶ Z :=
    SSet.ex.map (lastVertex.app B) ≫ sqZ.lift
  have hsq : d ≫ p = relativeCanonicalExtension (SSet.sd.map i) ≫ qB := by
    apply pushout.hom_ext
    · change (pushout.inl _ _ ≫ d) ≫ p =
        (pushout.inl _ _ ≫ relativeCanonicalExtension (SSet.sd.map i)) ≫ qB
      rw [pushout.inl_desc, relativeCanonicalExtension_inl, hf]
      change lastVertex.app B ≫ b = canonicalExtension.app (SSet.sd.obj B) ≫
        (SSet.ex.map (lastVertex.app B) ≫ sqZ.lift)
      rw [← Category.assoc, ← canonicalExtension.naturality, Category.assoc]
      change lastVertex.app B ≫ b = lastVertex.app B ≫
        (canonicalExtension.app B ≫ sqZ.lift)
      rw [sqZ.fac_left]
    · change (pushout.inr _ _ ≫ d) ≫ p =
        (pushout.inr _ _ ≫ relativeCanonicalExtension (SSet.sd.map i)) ≫ qB
      rw [pushout.inr_desc, relativeCanonicalExtension_inr]
      change (SSet.ex.map (lastVertex.app A) ≫ sqA.lift) ≫ p =
        SSet.ex.map (SSet.sd.map i) ≫ (SSet.ex.map (lastVertex.app B) ≫ sqZ.lift)
      rw [Category.assoc, sqA.fac_right]
      have hn : lastVertex.app A ≫ i = SSet.sd.map i ≫ lastVertex.app B :=
        (lastVertex.naturality i).symm
      change SSet.ex.map (lastVertex.app A) ≫ (SSet.ex.map i ≫ sqZ.lift) = _
      simp only [← Category.assoc, ← SSet.ex.map_comp]
      rw [hn]
  have := subdivision_map_mono i
  have hrel := relativeCanonicalExtension_anodyne (SSet.sd.map i) hSdA hSdB
  let : HasLiftingProperty (relativeCanonicalExtension (SSet.sd.map i)) p := hrel p hp
  let sqE : CommSq d (relativeCanonicalExtension (SSet.sd.map i)) p qB := ⟨hsq⟩
  have hr₀ : canonicalExtension.app (SSet.sd.obj B) ≫ sqE.lift = f := by
    rw [← relativeCanonicalExtension_inl (SSet.sd.map i), Category.assoc, sqE.fac_left]
    exact pushout.inl_desc f qA hq
  have hr₁ : SSet.ex.map (SSet.sd.map i) ≫ sqE.lift = qA := by
    rw [← relativeCanonicalExtension_inr (SSet.sd.map i), Category.assoc, sqE.fac_left]
    exact pushout.inr_desc f qA hq
  let g : B ⟶ E := SSet.sdExAdjunction.unit.app B ≫ sqE.lift
  have hgi : i ≫ g = a := by
    have hn : i ≫ SSet.sdExAdjunction.unit.app B =
        SSet.sdExAdjunction.unit.app A ≫ SSet.ex.map (SSet.sd.map i) :=
      SSet.sdExAdjunction.unit.naturality i
    change i ≫ (SSet.sdExAdjunction.unit.app B ≫ sqE.lift) = a
    rw [← Category.assoc, hn, Category.assoc, hr₁]
    change SSet.sdExAdjunction.unit.app A ≫
      (SSet.ex.map (lastVertex.app A) ≫ sqA.lift) = a
    rw [← Category.assoc, subdivision_unit_extension_lastVertex, sqA.fac_left]
  have hgp : g ≫ p = b := by
    change (SSet.sdExAdjunction.unit.app B ≫ sqE.lift) ≫ p = b
    rw [Category.assoc, sqE.fac_right]
    change SSet.sdExAdjunction.unit.app B ≫
      (SSet.ex.map (lastVertex.app B) ≫ sqZ.lift) = b
    rw [← Category.assoc, subdivision_unit_extension_lastVertex, sqZ.fac_left]
  let H₀ := postcomposeSimplicialHomotopy (subdivisionUnitHomotopy B) sqE.lift
  let H : SSet.Homotopy (lastVertex.app B ≫ g) f :=
    { h := H₀.h
      h₀ := H₀.h₀.trans (Category.assoc _ _ _)
      h₁ := H₀.h₁.trans hr₀
      rel := H₀.rel }
  refine ⟨g, H, hgi, hgp, ?_, ?_⟩
  · change (SSet.sd.map i ▷ Δ[1]) ≫ ((subdivisionUnitHomotopy B).h ≫ sqE.lift) = _
    rw [← Category.assoc, subdivisionUnitHomotopy_naturality, Category.assoc, hr₁]
    change (subdivisionUnitHomotopy A).h ≫
      (SSet.ex.map (lastVertex.app A) ≫ sqA.lift) = _
    rw [← Category.assoc, subdivisionUnitHomotopy_stationary,
      Category.assoc, Category.assoc, sqA.fac_left]
  · change ((subdivisionUnitHomotopy B).h ≫ sqE.lift) ≫ p = _
    rw [Category.assoc, sqE.fac_right]
    change (subdivisionUnitHomotopy B).h ≫
      (SSet.ex.map (lastVertex.app B) ≫ sqZ.lift) = _
    rw [← Category.assoc, subdivisionUnitHomotopy_stationary,
      Category.assoc, Category.assoc, sqZ.fac_left]

theorem exists_simplexSubcomplex_subdivision_relative_base_descent {m n : ℕ}
    (A : (Δ[m] : SSet.{0}).Subcomplex) (B : (Δ[n] : SSet.{0}).Subcomplex)
    {E Z : SSet.{0}} [SSet.KanComplex Z] (i : A.toSSet ⟶ B.toSSet) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (a : A.toSSet ⟶ E) (f : SSet.sd.obj B.toSSet ⟶ E) (b : B.toSSet ⟶ Z)
    (ha : a ≫ p = i ≫ b) (hf : f ≫ p = lastVertex.app B.toSSet ≫ b)
    (hi : SSet.sd.map i ≫ f = lastVertex.app A.toSSet ≫ a) :
    ∃ (g : B.toSSet ⟶ E) (H : SSet.Homotopy (lastVertex.app B.toSSet ≫ g) f),
      i ≫ g = a ∧ g ≫ p = b ∧
      (SSet.sd.map i ▷ Δ[1]) ≫ H.h =
        fst (SSet.sd.obj A.toSSet) Δ[1] ≫ lastVertex.app A.toSSet ≫ a ∧
      H.h ≫ p = fst (SSet.sd.obj B.toSSet) Δ[1] ≫ lastVertex.app B.toSSet ≫ b :=
  exists_subdivision_relative_base_descent i p
    (canonicalExtension_simplexSubcomplex_anodyne A)
    (canonicalExtension_simplexSubcomplex_anodyne B)
    (canonicalExtension_subdivision_subcomplex_anodyne A)
    (canonicalExtension_subdivision_subcomplex_anodyne B) a f b ha hf hi

end

end Thomason.Construction

end

section

/-! # Exact relative descent from finite extension stages

Taking the inverse adjunct of one extension-stage solution gives a
subdivided solution.  Relative subdivision descent removes that stage
without changing either the original prescribed source or the base map.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

@[reassoc]
theorem stageUnit_naturality {E Z : SSet.{0}} (p : E ⟶ Z) (r : ℕ) :
    stageUnit E r ≫ stageMap p r = p ≫ stageUnit Z r :=
  (diagramMap p).naturality (homOfLE (Nat.zero_le r))

theorem exists_stage_relative_descent {A B E Z : SSet.{0}}
    [SSet.KanComplex Z] (i : A ⟶ B) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hA : SSet.anodyneExtensions (canonicalExtension.app A))
    (hB : SSet.anodyneExtensions (canonicalExtension.app B))
    (hSdA : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj A)))
    (hSdB : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj B)))
    (r : ℕ) (a : A ⟶ E) (f : B ⟶ stage E r) (b : B ⟶ Z)
    (ha : a ≫ p = i ≫ b)
    (hf : f ≫ stageMap p r = b ≫ stageUnit Z r)
    (hi : i ≫ f = a ≫ stageUnit E r) :
    ∃ g : B ⟶ E, i ≫ g = a ∧ g ≫ p = b := by
  induction r with
  | zero =>
    refine ⟨f, ?_, ?_⟩
    · simpa only [stageUnit_zero, Category.comp_id] using hi
    · simpa only [stageMap, stageUnit_zero, Category.comp_id] using hf
  | succ r ih =>
    let f' := (SSet.sdExAdjunction.homEquiv B (stage E r)).symm f
    have htranspose : SSet.sdExAdjunction.homEquiv B (stage E r) f' = f :=
      (SSet.sdExAdjunction.homEquiv B (stage E r)).apply_symm_apply f
    have hf' : f' ≫ stageMap p r = lastVertex.app B ≫ (b ≫ stageUnit Z r) := by
      apply (SSet.sdExAdjunction.homEquiv _ _).injective
      rw [SSet.sdExAdjunction.homEquiv_naturality_right, htranspose, canonicalExtension_adjunct]
      change f ≫ SSet.ex.map (stageMap p r) = b ≫ stageUnit Z (r+1) at hf
      simpa only [stageUnit_succ, Category.assoc] using hf
    have hi' : SSet.sd.map i ≫ f' = lastVertex.app A ≫ (a ≫ stageUnit E r) := by
      apply (SSet.sdExAdjunction.homEquiv _ _).injective
      rw [SSet.sdExAdjunction.homEquiv_naturality_left, htranspose, canonicalExtension_adjunct]
      simpa only [stageUnit_succ, Category.assoc] using hi
    have har : (a ≫ stageUnit E r) ≫ stageMap p r = i ≫ (b ≫ stageUnit Z r) := by
      rw [Category.assoc, stageUnit_naturality, ← Category.assoc, ha, Category.assoc]
    have : SSet.KanComplex (stage Z r) := stage_kan Z r
    have : HomotopicalAlgebra.Fibration (stageMap p r) := stageMap_fibration p r
    obtain ⟨g, _, hgi, hgp, _, _⟩ := exists_subdivision_relative_base_descent i
      (stageMap p r) hA hB hSdA hSdB (a ≫ stageUnit E r) f' (b ≫ stageUnit Z r)
      har hf' hi'
    exact ih g hgp hgi

theorem exists_stage_simplexSubcomplex_relative_descent {m n : ℕ}
    (A : (Δ[m] : SSet.{0}).Subcomplex) (B : (Δ[n] : SSet.{0}).Subcomplex)
    {E Z : SSet.{0}} [SSet.KanComplex Z] (i : A.toSSet ⟶ B.toSSet) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (r : ℕ) (a : A.toSSet ⟶ E) (f : B.toSSet ⟶ stage E r) (b : B.toSSet ⟶ Z)
    (ha : a ≫ p = i ≫ b)
    (hf : f ≫ stageMap p r = b ≫ stageUnit Z r)
    (hi : i ≫ f = a ≫ stageUnit E r) :
    ∃ g : B.toSSet ⟶ E, i ≫ g = a ∧ g ≫ p = b :=
  exists_stage_relative_descent i p
    (canonicalExtension_simplexSubcomplex_anodyne A)
    (canonicalExtension_simplexSubcomplex_anodyne B)
    (canonicalExtension_subdivision_subcomplex_anodyne A)
    (canonicalExtension_subdivision_subcomplex_anodyne B) r a f b ha hf hi

theorem exists_stage_boundary_descent (n : ℕ) {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (r : ℕ) (a : (SSet.boundary.{0} n).toSSet ⟶ E)
    (f : (Δ[n] : SSet.{0}) ⟶ stage E r) (b : (Δ[n] : SSet.{0}) ⟶ Z)
    (ha : a ≫ p = (SSet.boundary.{0} n).ι ≫ b)
    (hf : f ≫ stageMap p r = b ≫ stageUnit Z r)
    (hi : (SSet.boundary.{0} n).ι ≫ f = a ≫ stageUnit E r) :
    ∃ g : (Δ[n] : SSet.{0}) ⟶ E,
      (SSet.boundary.{0} n).ι ≫ g = a ∧ g ≫ p = b :=
  exists_stage_relative_descent (SSet.boundary.{0} n).ι p
    (canonicalExtension_boundary_anodyne n) (canonicalExtension_standard_anodyne n)
    (canonicalExtension_subdivision_boundary_anodyne n)
    (canonicalExtension_subdivision_standard_anodyne n) r a f b ha hf hi

/-- Finite support lets an exact original-boundary solution in the
infinite extension descend all the way into the original Kan fibration. -/
theorem exists_infinite_boundary_descent (n : ℕ) {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (a : (SSet.boundary.{0} n).toSSet ⟶ E)
    (f : (Δ[n] : SSet.{0}) ⟶ obj E) (b : (Δ[n] : SSet.{0}) ⟶ Z)
    (ha : a ≫ p = (SSet.boundary.{0} n).ι ≫ b)
    (hf : f ≫ map p = b ≫ unit Z)
    (hi : (SSet.boundary.{0} n).ι ≫ f = a ≫ unit E) :
    ∃ g : (Δ[n] : SSet.{0}) ⟶ E,
      (SSet.boundary.{0} n).ι ≫ g = a ∧ g ≫ p = b := by
  obtain ⟨r, g, hg, hi'⟩ := finite_relative_map_factors E (SSet.boundary.{0} n).ι a f hi
  have hf' : g ≫ stageMap p r = b ≫ stageUnit Z r := by
    apply (cancel_mono (inclusion Z r)).mp
    rw [Category.assoc, ← inclusion_map, ← Category.assoc, hg, hf, Category.assoc]
    exact congrArg (b ≫ ·) (colimit.w (diagram Z) (homOfLE (Nat.zero_le r))).symm
  exact exists_stage_boundary_descent n p r a g b ha hf' hi'

/-- On Kan fibrations over Kan bases, the actual infinite extension
reflects the boundary right lifting property. -/
theorem boundary_rlp_of_map {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p] (hp : I.rlp (map p)) : I.rlp p := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  refine ⟨fun {a b} sq => ?_⟩
  have : HasLiftingProperty (SSet.boundary.{0} n).ι (map p) := hp _ (boundary_ι_mem_I n)
  have hn : unit E ≫ map p = p ≫ unit Z := (coaugmentation.naturality p).symm
  let sq' : CommSq (a ≫ unit E) (SSet.boundary.{0} n).ι (map p) (b ≫ unit Z) := ⟨by
    rw [Category.assoc, hn, ← Category.assoc, sq.w, Category.assoc]⟩
  obtain ⟨g, hgi, hgp⟩ := exists_infinite_boundary_descent n p a sq'.lift b sq.w
    sq'.fac_right sq'.fac_left
  exact ⟨⟨{ l := g, fac_left := hgi, fac_right := hgp }⟩⟩

theorem map_boundary_rlp_iff {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p] : I.rlp (map p) ↔ I.rlp p :=
  ⟨boundary_rlp_of_map p, map_boundary_rlp p⟩

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Exact relative descent from every finite subdivision

For simplex subcomplexes, every finite subdivision has an anodyne
canonical extension.  Repeated relative descent therefore removes all
subdivisions while retaining the original boundary and base maps.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

theorem iteratedSubdivision_succ_obj (K : SSet.{0}) (r : ℕ) :
    (iteratedSubdivision (r+1)).obj K = (iteratedSubdivision r).obj (SSet.sd.obj K) := by
  induction r with
  | zero => rfl
  | succ r ih => exact congrArg SSet.sd.obj ih

@[reassoc]
theorem iteratedLastVertex_naturality {A B : SSet.{0}} (i : A ⟶ B) (r : ℕ) :
    (iteratedSubdivision r).map i ≫ iteratedLastVertex B r =
      iteratedLastVertex A r ≫ i := by
  induction r with
  | zero => exact (Category.comp_id i).trans (Category.id_comp i).symm
  | succ r ih =>
    have hn : SSet.sd.map ((iteratedSubdivision r).map i) ≫
        lastVertex.app ((iteratedSubdivision r).obj B) =
      lastVertex.app ((iteratedSubdivision r).obj A) ≫ (iteratedSubdivision r).map i :=
      lastVertex.naturality ((iteratedSubdivision r).map i)
    change SSet.sd.map ((iteratedSubdivision r).map i) ≫
        (lastVertex.app ((iteratedSubdivision r).obj B) ≫ iteratedLastVertex B r) =
      (lastVertex.app ((iteratedSubdivision r).obj A) ≫ iteratedLastVertex A r) ≫ i
    rw [← Category.assoc, hn, Category.assoc, ih, Category.assoc]

def subcomplexFirstSubdivisionIso {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.sd.obj A.toSSet ≅ nerve (faceFamilyVertices (subcomplexFaceFamily A)) :=
  SSet.sd.mapIso (SSet.Subcomplex.eqToIso (faceUnion_subcomplexFaceFamily A).symm) ≪≫
    faceUnionSubdivisionIso (subcomplexFaceFamily A)

theorem iteratedSubdivision_subcomplex_canonical_anodyne {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) (r : ℕ) :
    SSet.anodyneExtensions (canonicalExtension.app ((iteratedSubdivision r).obj A.toSSet)) := by
  cases r with
  | zero => exact canonicalExtension_simplexSubcomplex_anodyne A
  | succ r =>
    rw [iteratedSubdivision_succ_obj]
    have := finite_nonemptyFiniteChains (ULift.{0} (Fin (n+1)))
    exact canonicalExtension_anodyne_of_iso
      ((iteratedSubdivision r).mapIso (subcomplexFirstSubdivisionIso A))
      (iteratedSubdivision_canonical_anodyne
        (PartOrd.of (faceFamilyVertices (subcomplexFaceFamily A))) r)

theorem iteratedSubdivision_standard_canonical_anodyne (n r : ℕ) :
    SSet.anodyneExtensions
      (canonicalExtension.app ((iteratedSubdivision r).obj (Δ[n] : SSet.{0}))) := by
  exact canonicalExtension_anodyne_of_iso
    ((iteratedSubdivision r).mapIso (simplexNerveIso.app (.mk n)))
    (iteratedSubdivision_canonical_anodyne (PartOrd.of (ULift.{0} (Fin (n+1)))) r)

/-- A relative lift at any finite subdivision descends to a lift over the
original parameter.  The two equalities in the conclusion are literal. -/
theorem exists_iteratedSubdivision_relative_base_descent {A B E Z : SSet.{0}}
    [SSet.KanComplex Z] (i : A ⟶ B) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hA : ∀ r, SSet.anodyneExtensions
      (canonicalExtension.app ((iteratedSubdivision r).obj A)))
    (hB : ∀ r, SSet.anodyneExtensions
      (canonicalExtension.app ((iteratedSubdivision r).obj B)))
    (r : ℕ) (a : A ⟶ E) (f : (iteratedSubdivision r).obj B ⟶ E) (b : B ⟶ Z)
    (ha : a ≫ p = i ≫ b)
    (hf : f ≫ p = iteratedLastVertex B r ≫ b)
    (hi : (iteratedSubdivision r).map i ≫ f = iteratedLastVertex A r ≫ a) :
    ∃ g : B ⟶ E, i ≫ g = a ∧ g ≫ p = b := by
  induction r with
  | zero =>
    change i ≫ f = (𝟙 A) ≫ a at hi
    change f ≫ p = (𝟙 B) ≫ b at hf
    rw [Category.id_comp] at hi hf
    exact ⟨f, hi, hf⟩
  | succ r ih =>
    have := iteratedSubdivision_mono r i
    have har : (iteratedLastVertex A r ≫ a) ≫ p =
        (iteratedSubdivision r).map i ≫ (iteratedLastVertex B r ≫ b) := by
      rw [Category.assoc, ha, ← Category.assoc, ← iteratedLastVertex_naturality,
        Category.assoc]
    have hfr : f ≫ p = lastVertex.app ((iteratedSubdivision r).obj B) ≫
        (iteratedLastVertex B r ≫ b) := by
      change f ≫ p =
        (lastVertex.app ((iteratedSubdivision r).obj B) ≫ iteratedLastVertex B r) ≫ b at hf
      exact hf.trans (Category.assoc _ _ _)
    have hir : SSet.sd.map ((iteratedSubdivision r).map i) ≫ f =
        lastVertex.app ((iteratedSubdivision r).obj A) ≫ (iteratedLastVertex A r ≫ a) := by
      change SSet.sd.map ((iteratedSubdivision r).map i) ≫ f =
        (lastVertex.app ((iteratedSubdivision r).obj A) ≫ iteratedLastVertex A r) ≫ a at hi
      exact hi.trans (Category.assoc _ _ _)
    obtain ⟨g, _, hga, hgb, _, _⟩ := exists_subdivision_relative_base_descent
      ((iteratedSubdivision r).map i) p (hA r) (hB r) (hA (r+1)) (hB (r+1))
      (iteratedLastVertex A r ≫ a) f (iteratedLastVertex B r ≫ b) har hfr hir
    exact ih g hgb hga

theorem exists_iterated_simplexSubcomplex_relative_base_descent {m n : ℕ}
    (A : (Δ[m] : SSet.{0}).Subcomplex) (B : (Δ[n] : SSet.{0}).Subcomplex)
    {E Z : SSet.{0}} [SSet.KanComplex Z] (i : A.toSSet ⟶ B.toSSet) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (r : ℕ) (a : A.toSSet ⟶ E)
    (f : (iteratedSubdivision r).obj B.toSSet ⟶ E) (b : B.toSSet ⟶ Z)
    (ha : a ≫ p = i ≫ b)
    (hf : f ≫ p = iteratedLastVertex B.toSSet r ≫ b)
    (hi : (iteratedSubdivision r).map i ≫ f = iteratedLastVertex A.toSSet r ≫ a) :
    ∃ g : B.toSSet ⟶ E, i ≫ g = a ∧ g ≫ p = b :=
  exists_iteratedSubdivision_relative_base_descent i p
    (iteratedSubdivision_subcomplex_canonical_anodyne A)
    (iteratedSubdivision_subcomplex_canonical_anodyne B) r a f b ha hf hi

theorem exists_iterated_boundary_lift (n : ℕ) {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p] (r : ℕ)
    (a : (SSet.boundary.{0} n).toSSet ⟶ E)
    (f : (iteratedSubdivision r).obj (Δ[n] : SSet.{0}) ⟶ E)
    (b : (Δ[n] : SSet.{0}) ⟶ Z)
    (ha : a ≫ p = (SSet.boundary.{0} n).ι ≫ b)
    (hf : f ≫ p = iteratedLastVertex (Δ[n] : SSet.{0}) r ≫ b)
    (hi : (iteratedSubdivision r).map (SSet.boundary.{0} n).ι ≫ f =
      iteratedLastVertex (SSet.boundary.{0} n).toSSet r ≫ a) :
    ∃ g : (Δ[n] : SSet.{0}) ⟶ E,
      (SSet.boundary.{0} n).ι ≫ g = a ∧ g ≫ p = b :=
  exists_iteratedSubdivision_relative_base_descent (SSet.boundary.{0} n).ι p
    (iteratedSubdivision_subcomplex_canonical_anodyne (SSet.boundary.{0} n))
    (iteratedSubdivision_standard_canonical_anodyne n) r a f b ha hf hi

end

end Thomason.Construction

end

section

/-! # Simplicial approximation with a prescribed boundary comparison

A continuous extension of an order map has a finite simplicial
approximation whose restriction is simplicially homotopic to the exact
iterated last-vertex boundary. Kan lifting can therefore make the
boundary equality literal.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder
open CategoryTheory.Limits
open ChainLabelApproximation RelativeLabelCarrier

noncomputable section

theorem exists_poset_relative_approximation
    (A B : PartOrd.{0}) [Finite A] [Fintype B]
    {P : Type} [PartialOrder P]
    (i : A →o B) (hi : Function.Injective i) (g : A →o P)
    (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
    (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom z) :
    ∃ (r : ℕ) (f : (iteratedSubdivision r).obj (nerve B) ⟶ nerve P),
      Nonempty (SSet.Homotopy ((iteratedSubdivision r).map (nerveMap i.monotone.functor) ≫ f)
        (iteratedLastVertex (nerve A) r ≫ nerveMap g.monotone.functor)) := by
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels B P F
  have hvertex (v : iteratedChainPoset B r) :
      0 < (PosetGeometry.coordinates P
        (F (iteratedChainRealization B r (posetVertexPoint v)))).weights (label v) :=
    hl 0 (PosetGeometry.vertex v) (Convexity.StdSimplex.single 0) 0
  have hbound := boundary_label_le i hi g F hF r label hvertex
  let u : iteratedChainPoset A (r+1) →o P :=
    (greatestLabel label hlabel).comp (NonemptyFiniteChains.orderHomMap (iteratedMap i r))
  let v : iteratedChainPoset A (r+1) →o P :=
    g.comp (greatestVertex A (r+1))
  have huv (C : NonemptyFiniteChains (iteratedChainPoset A r)) : u C ≤ v C := by
    apply greatestLabel_le label hlabel
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff C (iteratedMap i r) y).mp hy
    exact (hbound x).trans (g.monotone ((greatestVertex A r).monotone
      (le_greatest C x hx)))
  let f : (iteratedSubdivision (r+1)).obj (nerve B) ⟶ nerve P :=
    (iteratedSubdivisionNerveIso B (r+1)).hom ≫ nerveMapOfLabels label hlabel
  have hf : (iteratedSubdivision (r+1)).map (nerveMap i.monotone.functor) ≫ f =
      (iteratedSubdivisionNerveIso A (r+1)).hom ≫ nerveMap u.monotone.functor := by
    have hu : nerveMap u.monotone.functor =
        nerveMap (iteratedMap i (r+1)).monotone.functor ≫ nerveMapOfLabels label hlabel :=
      orderNerveMap_comp (NonemptyFiniteChains.orderHomMap (iteratedMap i r))
        (greatestLabel label hlabel)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ nerveMapOfLabels label hlabel)
        (iteratedSubdivisionNerveIso_naturality i (r+1))).trans
          ((Category.assoc _ _ _).trans
            (congrArg ((iteratedSubdivisionNerveIso A (r+1)).hom ≫ ·) hu.symm)))
  have hv : (iteratedSubdivisionNerveIso A (r+1)).hom ≫ nerveMap v.monotone.functor =
      iteratedLastVertex (nerve A) (r+1) ≫ nerveMap g.monotone.functor := by
    dsimp only [v]
    rw [orderNerveMap_comp, ← Category.assoc, greatestVertex_lastVertex]
  refine ⟨r+1, f, ?_⟩
  rw [hf, ← hv]
  have H := whiskerSimplicialHomotopy (iteratedSubdivisionNerveIso A (r+1)).hom
      (orderNerveHomotopy u v huv) (𝟙 _)
  exact ⟨by simpa only [Category.comp_id] using H⟩

/-- A continuous relative extension in a poset realization gives an
exact simplicial extension after any map into a Kan target. All finite
subdivisions and the boundary homotopy are removed in that same target. -/
theorem kan_extension_of_poset_realization_extension
    (A B : PartOrd.{0}) [Finite A] [Fintype B]
    {P : Type} [PartialOrder P]
    (i : A →o B) (hi : Function.Injective i) (g : A →o P)
    (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
    (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
    {X : SSet.{0}} [SSet.KanComplex X] (k : nerve P ⟶ X) :
    ∃ d : nerve B ⟶ X, nerveMap i.monotone.functor ≫ d =
      nerveMap g.monotone.functor ≫ k := by
  let : SSet.KanComplex (⊤_ SSet.{0}) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr (fun _ _ _ _ => by
      rw [show terminal.from (⊤_ SSet.{0}) = 𝟙 _ from terminal.hom_ext _ _]
      infer_instance)
  let j := nerveMap i.monotone.functor
  let : Mono j := SubdivisionHornFaces.nerveMap_mono i hi
  obtain ⟨r, f, ⟨H⟩⟩ := exists_poset_relative_approximation A B i hi g F hF
  let jr := (iteratedSubdivision r).map j
  let : Mono jr := iteratedSubdivision_mono r j
  have H' : SSet.Homotopy (jr ≫ (f ≫ k))
      (iteratedLastVertex (nerve A) r ≫ (nerveMap g.monotone.functor ≫ k)) := by
    simpa only [Category.id_comp, Category.assoc] using
      whiskerSimplicialHomotopy (𝟙 _) H k
  obtain ⟨fr, hfr, _⟩ := kan_lift_of_boundary_homotopy jr (terminal.from X)
    (f ≫ k) (terminal.from _) (terminal.hom_ext _ _)
    (iteratedLastVertex (nerve A) r ≫ (nerveMap g.monotone.functor ≫ k))
    H' (terminal.hom_ext _ _)
  obtain ⟨d, hd, _⟩ := exists_iteratedSubdivision_relative_base_descent j (terminal.from X)
    (iteratedSubdivision_canonical_anodyne A)
    (iteratedSubdivision_canonical_anodyne B) r
    (nerveMap g.monotone.functor ≫ k) fr (terminal.from _)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _) hfr
  exact ⟨d, hd⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Exact Kan extensions from finite relative realization lifts

The finite nonsingular resolution and the relative approximation theorem
are composed here. The resulting extension takes values in the original
Kan complex, with an exact boundary equation.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open SubdivisionBarycentric NonsingularLastVertex

noncomputable section

theorem kan_extension_on_resolved_facePoset {A B X : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite] [SSet.KanComplex X]
    (i : nerve A.N ⟶ B) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (map A ≫ a) = SSet.toTop.map i ≫ b) :
    ∃ d : nerve B.N ⟶ X,
      nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor ≫ d =
        map (nerve A.N) ≫ map A ≫ a := by
  let : (nerve A.N).Finite := SSet.finite_of_mono i
  obtain ⟨S, hS, a', ha', c, _, hc, he⟩ :=
    FaceSimplexResolution.finite_relative_order_lift i a b h
  let : SSet.Finite S.toSSet := hS
  let : Fintype B.N := Fintype.ofFinite _
  let j := faceMap i (preservesNondegenerate_of_mono i)
  let g := faceMap a' ha'
  let k : nerve S.toSSet.N ⟶ X :=
    map S.toSSet ≫ S.ι ≫ FaceSimplexResolution.augmentation X
  obtain ⟨d, hd⟩ := kan_extension_of_poset_realization_extension
    (PartOrd.of (nerve A.N).N) (PartOrd.of B.N) j (faceMap_injective i) g c.hom
    (fun z => congrArg (fun f => f.hom z) hc) k
  refine ⟨d, hd.trans ?_⟩
  exact he

/-- A continuous extension across a finite nonsingular inclusion gives an
exact simplicial extension on its face-poset nerve. The boundary is the
specified last-vertex comparison followed by the original map. -/
theorem kan_extension_on_facePoset {A B X : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite] [SSet.KanComplex X]
    (i : A ⟶ B) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map i ≫ b = SSet.toTop.map a) :
    ∃ d : nerve B.N ⟶ X,
      nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor ≫ d =
        map A ≫ a := by
  let : A.Finite := SSet.finite_of_mono i
  let : (nerve B.N).Finite := PosetGeometry.nerve_finite B.N
  let j := nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor
  let : Mono j := faceMap_nerve_mono i
  have hs : SSet.toTop.map (map A ≫ a) =
      SSet.toTop.map j ≫ (SSet.toTop.map (map B) ≫ b) := by
    have hj := congrArg SSet.toTop.map (map_naturality i (preservesNondegenerate_of_mono i))
    simp only [SSet.toTop.map_comp] at hj
    rw [← Category.assoc, hj, Category.assoc, h, ← SSet.toTop.map_comp]
  obtain ⟨d, hd⟩ := kan_extension_on_resolved_facePoset j a
    (SSet.toTop.map (map B) ≫ b) hs
  let f := (NerveFaceChains.subdivisionIso B.N).hom ≫ d
  have hf : SSet.sd.map j ≫ f = lastVertex.app (nerve A.N) ≫ (map A ≫ a) := by
    change SSet.sd.map j ≫ ((NerveFaceChains.subdivisionIso B.N).hom ≫ d) = _
    rw [← Category.assoc, NerveFaceChains.subdivisionIso_naturality
      (faceMap i (preservesNondegenerate_of_mono i)) (preservesNondegenerate_of_mono j),
      Category.assoc, hd, ← Category.assoc, NerveFaceChains.subdivisionIso_lastVertex]
  obtain ⟨e, _, he, _⟩ := exists_finitePoset_subdivision_domain_relative_descent j
    (map A ≫ a) f hf
  exact ⟨e, he⟩

end

end Thomason.Construction

end

end OAI
