import OAI.CategoryTheory.Thomason.Gray.FixedPathCylinders
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.KanSimplexContinuousFibers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import OAI.CategoryTheory.Thomason.Simplicial.SingularAcyclicFibers
import OAI.CategoryTheory.Thomason.Simplicial.SingularCubeNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

namespace OAI

section

/-! # Subdivision carries every horn inclusion to an anodyne map -/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

def hornFacets (n : ℕ) (k : Fin (n + 2)) : Finset (Finset (Fin (n + 2))) :=
  (Finset.univ.erase k).image (fun j => {j}ᶜ)

theorem faceUnion_hornFacets (n : ℕ) (k : Fin (n + 2)) :
    faceUnion (hornFacets n k) = SSet.horn.{0} (n+1) k := by
  classical
  ext d s
  simp [faceUnion, hornFacets, Finset.sup_eq_iSup,
    SSet.horn_eq_iSup]

def hornFaceSet (n : ℕ) (k : Fin (n + 2)) : Set (SubdivisionHornFaces.Faces n) :=
  {A | A.finset ≠ SubdivisionHornFaces.omitted n k ∧ A.finset ≠ Finset.univ}

theorem hornFaceSet_iff (n : ℕ) (k : Fin (n + 2))
    (A : SubdivisionHornFaces.Faces n) :
    A ∈ hornFaceSet n k ↔ ∃ j : Fin (n+2), j ≠ k ∧ ULift.up j ∉ A.finset := by
  constructor
  · intro h
    by_contra! he
    have hm : SubdivisionHornFaces.omitted n k ⊆ A.finset := by
      intro a ha
      exact he a.down (fun e => (Finset.mem_erase.mp ha).1 (by apply ULift.ext; exact e))
    exact (SubdivisionHornFaces.omitted_subset_cases n k A.finset hm).elim h.1 h.2
  · rintro ⟨j, hj, ha⟩
    constructor
    · intro he
      apply ha
      rw [he]
      exact Finset.mem_erase.mpr ⟨fun h => hj (congrArg ULift.down h), Finset.mem_univ _⟩
    · intro he
      exact ha (he ▸ Finset.mem_univ _)

theorem subdivided_hornFacets (n : ℕ) (k : Fin (n + 2)) :
    subdividedFaceUnion (hornFacets n k) = fullSubposetComplex (hornFaceSet n k) := by
  classical
  ext d s
  have hs : s ∈ (subdividedFaceUnion (hornFacets n k)).obj d ↔
      ∃ j : Fin (n+2), j ≠ k ∧
        ∀ i, ∀ x ∈ (s.obj i).finset, x.down ≠ j := by
    change s ∈ ((hornFacets n k).sup subdividedFace).obj d ↔ _
    unfold hornFacets
    rw [Finset.sup_image]
    simp only [Function.comp_apply, Finset.sup_eq_iSup, Subfunctor.iSup_obj,
      Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    simp [subdividedFace, fullSubposetComplex, chainsSupported]
    rfl
  rw [hs]
  constructor
  · rintro ⟨j, hj, ha⟩ i
    apply (hornFaceSet_iff n k (s.obj i)).mpr
    exact ⟨j, hj, fun hm => ha i (ULift.up j) hm rfl⟩
  · intro ha
    obtain ⟨j, hj, hm⟩ := (hornFaceSet_iff n k (s.obj (Fin.last d.unop.len))).mp
      (ha (Fin.last d.unop.len))
    refine ⟨j, hj, fun i x hx he => ?_⟩
    apply hm
    have hle := leOfHom (s.map (homOfLE (Fin.le_last i)))
    have hex : x = ULift.up j := by apply ULift.ext; exact he
    exact hex ▸ hle hx

theorem subdivision_horn_range (n : ℕ) (k : Fin (n + 2)) :
    SSet.Subcomplex.range (subdivisionInclusion (SSet.horn.{0} (n+1) k)) =
      fullSubposetComplex (hornFaceSet n k) := by
  rw [← faceUnion_hornFacets]
  rw [(finiteFaceUnion_mono_range (hornFacets n k)).2, subdivided_hornFacets]

theorem hornFaceNerve_range (n : ℕ) (k : Fin (n + 2)) :
    SSet.Subcomplex.range (nerveMap
      ((SubdivisionHornFaces.remainderInclusion n k).comp
        (SubdivisionHornFaces.inclusion n k)).monotone.functor) =
      fullSubposetComplex (hornFaceSet n k) := by
  ext d s
  constructor
  · rintro ⟨t, rfl⟩ i
    exact ⟨(t.obj i).val.property, (t.obj i).property⟩
  · intro hs
    let t : (nerve (SubdivisionHornFaces.HornFaces n k)).obj d := {
      obj i := ⟨⟨s.obj i, (hs i).1⟩, (hs i).2⟩
      map f := homOfLE (leOfHom (s.map f)) }
    exact ⟨t, nerve.ext_of_isThin rfl⟩

/-- The actual left-Kan-extension subdivision sends every generating horn
inclusion to an anodyne map, by the explicit finite face-poset collapse. -/
theorem subdivision_horn_anodyne (n : ℕ) (k : Fin (n + 2)) :
    SSet.anodyneExtensions (SSet.sd.map (SSet.horn.{0} (n+1) k).ι) := by
  let g := nerveMap ((SubdivisionHornFaces.remainderInclusion n k).comp
    (SubdivisionHornFaces.inclusion n k)).monotone.functor
  have hg : SSet.anodyneExtensions g :=
    SubdivisionHornFaces.full_hornFaces_inclusion_anodyne n k
  have : Mono g := SubdivisionHornFaces.nerveMap_mono _ (by
    intro a b h
    exact Subtype.ext (Subtype.ext h))
  have hgι : SSet.anodyneExtensions (SSet.Subcomplex.range g).ι := by
    have he : inv (SSet.Subcomplex.toRange g) ≫ g = (SSet.Subcomplex.range g).ι := by
      calc
        _ = inv (SSet.Subcomplex.toRange g) ≫
            (SSet.Subcomplex.toRange g ≫ (SSet.Subcomplex.range g).ι) :=
          congrArg (fun q => inv (SSet.Subcomplex.toRange g) ≫ q)
            (SSet.Subcomplex.toRange_ι g).symm
        _ = _ := IsIso.inv_hom_id_assoc _ _
    rw [← he]
    exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _) hg
  let f := subdivisionInclusion (SSet.horn.{0} (n+1) k)
  have : Mono f := by
    change Mono (subdivisionInclusion (SSet.horn.{0} (n+1) k))
    rw [← faceUnion_hornFacets]
    exact (finiteFaceUnion_mono_range (hornFacets n k)).1
  have hrange : SSet.Subcomplex.range f = SSet.Subcomplex.range g :=
    (subdivision_horn_range n k).trans (hornFaceNerve_range n k).symm
  have hf : SSet.anodyneExtensions f := by
    rw [← SSet.Subcomplex.toRange_ι f]
    apply SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    rw [hrange]
    exact hgι
  have he : f ≫ SSet.stdSimplex.sdIso.inv.app ⦋n+1⦌ =
      SSet.sd.map (SSet.horn.{0} (n+1) k).ι := by
    dsimp [f, subdivisionInclusion]
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [← he]
  exact SSet.anodyneExtensions.comp_mem _ _ hf (SSet.anodyneExtensions.of_isIso _)

end

end Thomason.Construction

end

section

/-! # Actual singular comparison for weakly contractible spaces -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- The map to a point is a singular Kan fibration for every topological space. -/
theorem singular_to_point_fibration (T : TopCat.{0}) :
    HomotopicalAlgebra.Fibration
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const T ()) : T ⟶ TopCat.of Unit)) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  rintro A B i hi
  simp only [J, CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  refine ⟨fun {a b} _ => ⟨⟨{
    l := singularHornFiller T j a
    fac_left := singularHornFiller_fac T j a
    fac_right := ?_ }⟩⟩⟩
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  apply (TopCat.toSSetObjEquiv (TopCat.of Unit) m).injective
  apply ContinuousMap.ext
  intro t
  exact Subsingleton.elim _ _

/-- Weak contractibility suffices for the actual singular-realization
comparison; no contraction or global counit-W theorem is assumed. -/
theorem singular_counit_weak_of_weaklyContractible (X : TopCat.{0})
    (hX : IsWeakHomotopyEquivalence (ContinuousMap.const X ())) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app X) := by
  let p : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map p) := singular_to_point_fibration X
  have hp : topologicalWeakEquivalences p := hX
  have hs : topologicalWeakEquivalences (SSet.toTop.map (TopCat.toSSet.map p)) :=
    (singular_fibration_weak_iff p).mpr hX
  have hU : topologicalWeakEquivalences (sSetTopAdj.counit.app (TopCat.of Unit)) :=
    singular_counit_weak_contractible _
  apply topologicalWeakEquivalences.of_postcomp (sSetTopAdj.counit.app X) p hp
  have hn : SSet.toTop.map (TopCat.toSSet.map p) ≫
      sSetTopAdj.counit.app (TopCat.of Unit) = sSetTopAdj.counit.app X ≫ p :=
    sSetTopAdj.counit.naturality p
  rw [← hn]
  exact topologicalWeakEquivalences.comp_mem _ _ hs hU

end

end Thomason.Construction

end

section

/-! # Anodyne homotopy extension with both variable endpoints prescribed -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem singular_point_hom_ext {K : SSet.{0}}
    (f g : K ⟶ TopCat.toSSet.obj (TopCat.of Unit)) : f = g := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  apply (TopCat.toSSetObjEquiv (TopCat.of Unit) m).injective
  apply ContinuousMap.ext
  intro t
  exact Subsingleton.elim _ _

/-- A homotopy over an anodyne parameter inclusion extends while preserving
both arbitrary endpoint maps on the entire target parameter object. -/
theorem singular_anodyne_endpoint_extension {A K : SSet.{0}} (i : A ⟶ K)
    (hi : SSet.anodyneExtensions i) (Y : TopCat.{0})
    (f₀ f₁ : K ⟶ TopCat.toSSet.obj Y)
    (a : A ⊗ Δ[1] ⟶ TopCat.toSSet.obj Y)
    (ha₀ : SSet.ι₀ ≫ a = i ≫ f₀) (ha₁ : SSet.ι₁ ≫ a = i ≫ f₁) :
    ∃ e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj Y,
      i ▷ Δ[1] ≫ e = a ∧ SSet.ι₀ ≫ e = f₀ ∧ SSet.ι₁ ≫ e = f₁ := by
  let p : Y ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const Y ())
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map p) := singular_to_point_fibration Y
  let c := intervalBoundaryFamily f₀ f₁
  let b := f₀ ≫ TopCat.toSSet.map p
  have hc : i ▷ (SSet.boundary 1 : SSet.{0}) ≫ c = A ◁ (SSet.boundary 1).ι ≫ a := by
    rw [intervalBoundaryFamily_naturality, intervalBoundaryFamily_restriction, ha₀, ha₁]
  obtain ⟨e, hei, hec, _⟩ := exists_kan_boundary_cylinder_lift i hi (TopCat.toSSet.map p)
    a c (CartesianMonoidalCategory.fst K Δ[1] ≫ b) hc
    (singular_point_hom_ext _ _) (singular_point_hom_ext _ _)
  obtain ⟨he₀, he₁⟩ := intervalBoundaryFamily_endpoints e f₀ f₁ hec
  exact ⟨e, hei, he₀, he₁⟩

/-- The endpoint-preserving extension evaluated on actual realizations. -/
theorem realization_anodyne_endpoint_extension {A K : SSet.{0}} (i : A ⟶ K)
    (hi : SSet.anodyneExtensions i) {Y : TopCat.{0}}
    (f₀ f₁ : SSet.toTop.obj K ⟶ Y)
    (a : C(unitInterval × SSet.toTop.obj A, Y))
    (ha₀ : ∀ z, a (0, z) = f₀.hom ((SSet.toTop.map i).hom z))
    (ha₁ : ∀ z, a (1, z) = f₁.hom ((SSet.toTop.map i).hom z)) :
    ∃ e : C(unitInterval × SSet.toTop.obj K, Y),
      (∀ t z, e (t, (SSet.toTop.map i).hom z) = a (t, z)) ∧
      (∀ z, e (0, z) = f₀.hom z) ∧ ∀ z, e (1, z) = f₁.hom z := by
  have h₀ : SSet.ι₀ ≫ singularCylinderMap a = i ≫ sSetTopAdj.homEquiv K Y f₀ := by
    rw [singularCylinderMap_zero, ← sSetTopAdj.homEquiv_naturality_left]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact ha₀
  have h₁ : SSet.ι₁ ≫ singularCylinderMap a = i ≫ sSetTopAdj.homEquiv K Y f₁ := by
    rw [singularCylinderMap_one, ← sSetTopAdj.homEquiv_naturality_left]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact ha₁
  obtain ⟨e, hei, he₀, he₁⟩ := singular_anodyne_endpoint_extension i hi Y
    (sSetTopAdj.homEquiv K Y f₀) (sSetTopAdj.homEquiv K Y f₁) (singularCylinderMap a) h₀ h₁
  refine ⟨evaluateSingularCylinder e, ?_, ?_, ?_⟩
  · intro t z
    rw [evaluateSingularCylinder_naturality, hei, evaluate_singularCylinderMap]
  · intro z
    rw [evaluateSingularCylinder_zero, he₀]
    exact congrArg (fun f => f.hom z) ((sSetTopAdj.homEquiv K Y).symm_apply_apply f₀)
  · intro z
    rw [evaluateSingularCylinder_one, he₁]
    exact congrArg (fun f => f.hom z) ((sSetTopAdj.homEquiv K Y).symm_apply_apply f₁)

end

end Thomason.Construction

end

section

/-! # Homotopies between lifts through an acyclic singular fibration -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Two simplicial lifts through a boundary-trivial fibration are connected
by one simplicial cylinder, still over the same base map. -/
theorem boundary_rlp_lifts_homotopic {X Y K : SSet.{0}} (p : X ⟶ Y)
    (hp : I.rlp p) (f₀ f₁ : K ⟶ X) (he : f₀ ≫ p = f₁ ≫ p) :
    ∃ H : K ⊗ Δ[1] ⟶ X,
      SSet.ι₀ ≫ H = f₀ ∧ SSet.ι₁ ≫ H = f₁ ∧
      H ≫ p = fst K Δ[1] ≫ f₀ ≫ p := by
  have hm : (MorphismProperty.monomorphisms SSet.{0}).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  let i := K ◁ (SSet.boundary 1).ι
  let a := intervalBoundaryFamily f₀ f₁
  let b := fst K Δ[1] ≫ f₀ ≫ p
  have hc : a ≫ p = i ≫ b := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro z
    change p.app m (if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0
      then f₀.app m z.1 else f₁.app m z.1) = p.app m (f₀.app m z.1)
    split_ifs
    · rfl
    · exact congrArg (fun t => t.app m z.1) he.symm
  let : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [mono_iff_injective]
    intro x y h
    change (x.1, x.2.val) = (y.1, y.2.val) at h
    have h' := Prod.mk.inj h
    exact Prod.ext h'.1 (Subtype.ext h'.2)
  let : HasLiftingProperty i p := hm i (by infer_instance)
  let sq : CommSq a i p b := ⟨hc⟩
  obtain ⟨h₀, h₁⟩ := intervalBoundaryFamily_endpoints sq.lift f₀ f₁ sq.fac_left
  exact ⟨sq.lift, h₀, h₁, sq.fac_right⟩

/-- Two continuous lifts from any actual realization through a singular
Kan fibration which is weak are homotopic. -/
theorem singular_acyclic_lifts_homotopic {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (K : SSet.{0})
    (f₀ f₁ : SSet.toTop.obj K ⟶ X) (he : f₀ ≫ p = f₁ ≫ p) :
    Nonempty (f₀.hom.Homotopy f₁.hom) := by
  let a₀ := sSetTopAdj.homEquiv K X f₀
  let a₁ := sSetTopAdj.homEquiv K X f₁
  have ha : a₀ ≫ TopCat.toSSet.map p = a₁ ≫ TopCat.toSSet.map p := by
    dsimp [a₀, a₁]
    rw [← sSetTopAdj.homEquiv_naturality_right,
      ← sSetTopAdj.homEquiv_naturality_right, he]
  obtain ⟨H, h₀, h₁, _⟩ := boundary_rlp_lifts_homotopic (TopCat.toSSet.map p)
    (singular_fibration_boundary_rlp p hp) a₀ a₁ ha
  exact ⟨{
    toContinuousMap := evaluateSingularCylinder H
    map_zero_left := fun x => by
      change evaluateSingularCylinder H (0, x) = _
      rw [evaluateSingularCylinder_zero, h₀]
      exact congrArg (fun t => t.hom x) ((sSetTopAdj.homEquiv K X).symm_apply_apply f₀)
    map_one_left := fun x => by
      change evaluateSingularCylinder H (1, x) = _
      rw [evaluateSingularCylinder_one, h₁]
      exact congrArg (fun t => t.hom x) ((sSetTopAdj.homEquiv K X).symm_apply_apply f₁) }⟩

/-- Maps from realizations lift through acyclic singular fibrations, even
when the target map is not itself a realized simplicial map. -/
theorem singular_acyclic_realized_lift {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (K : SSet.{0})
    (b : SSet.toTop.obj K ⟶ Y) :
    ∃ a : SSet.toTop.obj K ⟶ X, a ≫ p = b := by
  have hm : (MorphismProperty.monomorphisms SSet.{0}).rlp (TopCat.toSSet.map p) := by
    rw [SSet.rlp_monomorphisms]
    exact singular_fibration_boundary_rlp p hp
  let i := (⊥ : K.Subcomplex).ι
  let a : (⊥ : K.Subcomplex).toSSet ⟶ TopCat.toSSet.obj X :=
    SSet.Subcomplex.isInitialBot.to _
  let b' := sSetTopAdj.homEquiv K Y b
  let : HasLiftingProperty i (TopCat.toSSet.map p) := hm i (by dsimp [i]; infer_instance)
  let sq : CommSq a i (TopCat.toSSet.map p) b' :=
    ⟨SSet.Subcomplex.isInitialBot.hom_ext _ _⟩
  refine ⟨(sSetTopAdj.homEquiv K X).symm sq.lift, ?_⟩
  apply (sSetTopAdj.homEquiv K Y).injective
  rw [sSetTopAdj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact sq.fac_right

end

end Thomason.Construction

end

section

/-! # Singular Kan lifting for the actual mapping-path projection -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Mapping-path projections lift every anodyne simplicial parameter extension. -/
theorem mappingPath_singular_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    {A K : SSet.{0}} (i : A ⟶ K) (hi : SSet.anodyneExtensions i) :
    HasLiftingProperty i (TopCat.toSSet.map (mappingPathProjection p)) := by
  refine ⟨fun {a b} sq => ?_⟩
  let pt : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map pt) := singular_to_point_fibration X
  let : HasLiftingProperty i (TopCat.toSSet.map pt) :=
    hi _ ((fibration_iff _).mp inferInstance)
  let aX := a ≫ TopCat.toSSet.map (mappingPathRetraction p)
  let bPt : K ⟶ TopCat.toSSet.obj (TopCat.of Unit) :=
    SSet.const (TopCat.toSSetObj₀Equiv.symm ())
  let sqX : CommSq aX i (TopCat.toSSet.map pt) bPt :=
    ⟨singular_point_hom_ext _ _⟩
  let f : SSet.toTop.obj K ⟶ X := (sSetTopAdj.homEquiv K X).symm sqX.lift
  let a' : SSet.toTop.obj A ⟶ mappingPathSpace p :=
    (sSetTopAdj.homEquiv A _).symm a
  let b' : SSet.toTop.obj K ⟶ Y := (sSetTopAdj.homEquiv K Y).symm b
  have hf : SSet.toTop.map i ≫ f = a' ≫ mappingPathRetraction p := by
    have h := congrArg (sSetTopAdj.homEquiv A X).symm sqX.fac_left
    rw [sSetTopAdj.homEquiv_naturality_left_symm,
      sSetTopAdj.homEquiv_naturality_right_symm] at h
    exact h
  have hb : a' ≫ mappingPathProjection p = SSet.toTop.map i ≫ b' := by
    have h := congrArg (sSetTopAdj.homEquiv A Y).symm sq.w
    rw [sSetTopAdj.homEquiv_naturality_right_symm,
      sSetTopAdj.homEquiv_naturality_left_symm] at h
    exact h
  let H : C(unitInterval × SSet.toTop.obj A, Y) := {
    toFun z := (a'.hom z.2).val.2 z.1
    continuous_toFun := by fun_prop }
  have hH₀ (z : SSet.toTop.obj A) : H (0, z) = (f ≫ p).hom ((SSet.toTop.map i).hom z) := by
    change (a'.hom z).val.2 0 = p.hom (f.hom ((SSet.toTop.map i).hom z))
    rw [(a'.hom z).property]
    exact congrArg p.hom (congrArg (fun q => q.hom z) hf).symm
  have hH₁ (z : SSet.toTop.obj A) : H (1, z) = b'.hom ((SSet.toTop.map i).hom z) :=
    congrArg (fun q => q.hom z) hb
  obtain ⟨e, hei, he₀, he₁⟩ := realization_anodyne_endpoint_extension i hi (f ≫ p) b' H hH₀ hH₁
  let paths : C(SSet.toTop.obj K, C(unitInterval, Y)) := (e.comp ContinuousMap.prodSwap).curry
  let g : SSet.toTop.obj K ⟶ mappingPathSpace p := TopCat.ofHom {
    toFun z := ⟨(f.hom z, paths z), he₀ z⟩
    continuous_toFun := (f.hom.continuous.prodMk paths.continuous).subtype_mk
      (fun z => he₀ z) }
  have hgA : SSet.toTop.map i ≫ g = a' := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q => q.hom z) hf
    · apply ContinuousMap.ext
      intro t
      exact hei t z
  have hgB : g ≫ mappingPathProjection p = b' := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact he₁
  refine ⟨⟨{ l := sSetTopAdj.homEquiv K _ g, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← sSetTopAdj.homEquiv_naturality_left, hgA]
    exact (sSetTopAdj.homEquiv A _).apply_symm_apply a
  · rw [← sSetTopAdj.homEquiv_naturality_right, hgB]
    exact (sSetTopAdj.homEquiv K Y).apply_symm_apply b

/-- The endpoint projection is a genuine singular Kan fibration for every
continuous map, without any weak-equivalence hypothesis. -/
theorem mappingPath_singular_fibration {X Y : TopCat.{0}} (p : X ⟶ Y) :
    HomotopicalAlgebra.Fibration (TopCat.toSSet.map (mappingPathProjection p)) := by
  rw [fibration_iff]
  intro A K i hi
  apply mappingPath_singular_lifting p i
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact CategoryTheory.MorphismProperty.le_llp_rlp _ _ hi

end

end Thomason.Construction

end

section

/-! # Whitehead's theorem for the actual geometric realizations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- A weak map between geometric realizations has a constructed continuous
homotopy inverse. The proof uses the actual mapping-path fibration and the
proved singular boundary lifts, without a Kan–Quillen model structure. -/
def realizationWhiteheadEquiv {K L : SSet.{0}}
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hf : IsWeakHomotopyEquivalence f.hom) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (SSet.toTop.obj L) := by
  let q := mappingPathProjection f
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map q) := mappingPath_singular_fibration f
  have hq : IsWeakHomotopyEquivalence q.hom := (mappingPathProjection_weak_iff f).mpr hf
  let lift := singular_acyclic_realized_lift q hq L (𝟙 _)
  let s := Classical.choose lift
  have hs := Classical.choose_spec lift
  let j := mappingPathInclusion f
  let r := mappingPathRetraction f
  have he : (f ≫ s) ≫ q = j ≫ q := by
    rw [Category.assoc, hs, Category.comp_id]
    rfl
  let H := Classical.choice (singular_acyclic_lifts_homotopic q hq K (f ≫ s) j he)
  refine {
    toFun := f.hom
    invFun := (s ≫ r).hom
    left_inv := ⟨(ContinuousMap.Homotopy.refl r.hom).comp H⟩
    right_inv := ⟨{
      toFun := fun z => (s.hom z.2).val.2 z.1
      continuous_toFun := by fun_prop
      map_zero_left := fun y => (s.hom y).property
      map_one_left := fun y => ?_ }⟩ }
  exact congrArg (fun t => t.hom y) hs

/-- The actual weak test on a realized simplicial map is precisely the
existence of a homotopy equivalence with that same continuous forward map. -/
theorem realization_weak_iff_homotopyEquiv {K L : SSet.{0}} (f : K ⟶ L) :
    realizationWeakEquivalences f ↔
      ∃ e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (SSet.toTop.obj L),
        e.toFun = (SSet.toTop.map f).hom := by
  constructor
  · intro hf
    exact ⟨realizationWhiteheadEquiv (SSet.toTop.map f) hf, rfl⟩
  · rintro ⟨e, he⟩
    change IsWeakHomotopyEquivalence (SSet.toTop.map f).hom
    rw [← he]
    exact homotopyEquiv_isWeakHomotopyEquivalence e

end

end Thomason.Construction

end

section

/-! # Singularization preserves and reflects actual weak homotopy equivalences -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- The actual singular realization detects exactly the original topological
weak-equivalence test for every continuous map. The preservation direction
uses the constructed mapping-path factorization and full boundary lifting. -/
theorem singular_map_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    realizationWeakEquivalences (TopCat.toSSet.map p) ↔
      IsWeakHomotopyEquivalence p.hom := by
  constructor
  · exact singular_realization_reflects_weak p
  · intro hp
    let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map (mappingPathProjection p)) :=
      mappingPath_singular_fibration p
    have hq : realizationWeakEquivalences (TopCat.toSSet.map (mappingPathProjection p)) :=
      (singular_fibration_weak_iff _).mpr ((mappingPathProjection_weak_iff p).mpr hp)
    have hi : realizationWeakEquivalences (TopCat.toSSet.map (mappingPathInclusion p)) :=
      singular_homotopy_equivalence_weak (mappingPathEquiv p)
    have h := realizationWeakEquivalences.comp_mem _ _ hi hq
    rwa [← TopCat.toSSet.map_comp, mappingPath_factorization] at h

/-- The counit weak test transports along every actual weak homotopy
 equivalence, without requiring a chosen homotopy inverse. -/
theorem singular_counit_weak_iff_of_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : IsWeakHomotopyEquivalence p.hom) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app X) ↔
      topologicalWeakEquivalences (sSetTopAdj.counit.app Y) := by
  have hp' : topologicalWeakEquivalences p := hp
  have hs : topologicalWeakEquivalences (SSet.toTop.map (TopCat.toSSet.map p)) :=
    (singular_map_weak_iff p).mpr hp
  have hn : SSet.toTop.map (TopCat.toSSet.map p) ≫ sSetTopAdj.counit.app Y =
      sSetTopAdj.counit.app X ≫ p := sSetTopAdj.counit.naturality p
  constructor
  · intro hX
    apply topologicalWeakEquivalences.of_precomp _ _ hs
    rw [hn]
    exact topologicalWeakEquivalences.comp_mem _ _ hX hp'
  · intro hY
    apply topologicalWeakEquivalences.of_postcomp _ _ hp'
    rw [← hn]
    exact topologicalWeakEquivalences.comp_mem _ _ hs hY

end

end Thomason.Construction

end

section

/-! # Actual weak equivalences of singular fixed-endpoint internal paths -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory

noncomputable section

theorem fixedPathToInternal_postcomp {K : SSet.{0}} {X Y : TopCat.{0}}
    (p : X ⟶ Y) {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    fixedPathToInternal (f ≫ TopCat.toSSet.map
        (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) =
      fixedPathToInternal f ≫ fixedInternalPathMap (TopCat.toSSet.map p)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y) := by
  have he : internalPathTranspose (fixedPathCylinder
        (f ≫ TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) ) =
      internalPathTranspose (fixedPathCylinder f) ≫
        (ihom (SSet.stdSimplex.obj (SimplexCategory.mk 1))).map
          (TopCat.toSSet.map p) := by
    apply internalPathCylinder_injective
    rw [internalPathCylinder_transpose, internalPathCylinder_postcomp,
      internalPathCylinder_transpose, fixedPathCylinder_postcomp]
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  exact congrArg (fun q => q.app d z) he

/-- Naturality retains the specified endpoints under the actual singular
vertex identification, rather than choosing them up to paths. -/
theorem fixedPathInternalIso_naturality {X Y : TopCat.{0}} (p : X ⟶ Y) (x y : X) :
    TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y))) ≫
        (fixedPathInternalIso Y (p.hom x) (p.hom y)).hom =
      (fixedPathInternalIso X x y).hom ≫ fixedInternalPathMap (TopCat.toSSet.map p)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y) := by
  have h := fixedPathToInternal_naturality
    (TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) (𝟙 _)
  have h' := fixedPathToInternal_postcomp p (𝟙 (TopCat.toSSet.obj (TopCat.of (Path x y))))
  change _ ≫ fixedPathToInternal (𝟙 _) = fixedPathToInternal (𝟙 _) ≫ _
  have he := h.symm.trans h'
  convert he using 1
  constructor <;> intro hh <;> apply NatTrans.ext <;> funext d <;>
    apply ConcreteCategory.hom_ext <;> intro z <;> apply Subtype.ext <;>
    exact congrArg (fun k => (k.app d z).val) hh

def fixedPathInternalMapArrowIso {X Y : TopCat.{0}} (p : X ⟶ Y) (x y : X) :
    Arrow.mk (TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) ≅
      Arrow.mk (fixedInternalPathMap (TopCat.toSSet.map p)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) :=
  Arrow.isoMk (fixedPathInternalIso X x y) (fixedPathInternalIso Y (p.hom x) (p.hom y))
    (fixedPathInternalIso_naturality p x y).symm

/-- The fixed-endpoint internal-path map of an actual singular weak
map is a realization weak equivalence. This uses the proved dimension shift
for continuous fixed-path spaces and exact singular preservation of W. -/
theorem fixedInternalPathMap_singular_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) (x y : X) :
    realizationWeakEquivalences (fixedInternalPathMap (TopCat.toSSet.map p)
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) := by
  apply (realizationWeakEquivalences.arrow_mk_iso_iff (fixedPathInternalMapArrowIso p x y)).mp
  apply (singular_map_weak_iff _).mpr
  exact PathSpace.map_weak p.hom ((singular_map_weak_iff p).mp hp) x y

end

end Thomason.Construction

end

section

/-! # Exact continuous extension into homotopy fibres of weak maps -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- All actual homotopy fibres of a weak continuous map are weakly
contractible. This uses the constructed singular Kan mapping-path fibration. -/
theorem continuousHomotopyFiber_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : IsWeakHomotopyEquivalence p.hom) (b : Y) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (continuousHomotopyFiber p b) ()) := by
  have := mappingPath_singular_fibration p
  exact singular_fibration_fiber_weak (mappingPathProjection p)
    ((mappingPathProjection_weak_iff p).mpr hp) b

/-- In every dimension, a continuous boundary family in the genuine
homotopy fibre of a weak map extends exactly over the original realization. -/
theorem continuousHomotopyFiber_extension {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : IsWeakHomotopyEquivalence p.hom) (b : Y)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i]
    (a : SSet.toTop.obj K ⟶ continuousHomotopyFiber p b) :
    ∃ g : SSet.toTop.obj L ⟶ continuousHomotopyFiber p b,
      SSet.toTop.map i ≫ g = a := by
  have := mappingPath_singular_fibration p
  exact singular_fibration_fiber_extension (mappingPathProjection p)
    ((mappingPathProjection_weak_iff p).mpr hp) b i a

end

end Thomason.Construction

end

section

/-! # Finite exact continuous extensions inside every acyclic simplex fibre -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A weakly contractible space fills any realized monomorphism exactly.
The proof uses the already proved singular acyclic lifting theorem. -/
theorem weaklyContractible_realized_extension (T : TopCat.{0})
    (hT : IsWeakHomotopyEquivalence (ContinuousMap.const T ()))
    {A K : SSet.{0}} (i : A ⟶ K) [Mono i] (a : SSet.toTop.obj A ⟶ T) :
    ∃ c : SSet.toTop.obj K ⟶ T, SSet.toTop.map i ≫ c = a := by
  let p : T ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const T ())
  have : HomotopicalAlgebra.Fibration (TopCat.toSSet.map p) := singular_to_point_fibration T
  have : HasLiftingProperty (SSet.toTop.map i) p :=
    singular_fibration_realization_mono_lifting p hT i
  let sq : CommSq a (SSet.toTop.map i) p (TopCat.ofHom (ContinuousMap.const _ ())) := ⟨by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Every literal point fibre of an acyclic Kan map over a simplex is
weakly contractible, including fibres over nonvertex points. -/
theorem kan_acyclic_simplex_continuousFiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    IsWeakHomotopyEquivalence (ContinuousMap.const (continuousFiber (SSet.toTop.map p) b) ()) :=
  (kan_simplex_allPointFiberComparison_weak n p b).comp
    (continuousHomotopyFiber_weak (SSet.toTop.map p) hp b)

/-- Higher continuous boundary families extend EXACTLY inside a literal
fibre of an acyclic Kan simplex map. This is a geometric extension and
does not claim a simplicial filler. -/
theorem kan_acyclic_simplex_continuousFiber_extension {E A K : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (Δ[n] : SSet.{0}))
    (i : A ⟶ K) [Mono i]
    (a : SSet.toTop.obj A ⟶ continuousFiber (SSet.toTop.map p) b) :
    ∃ c : SSet.toTop.obj K ⟶ continuousFiber (SSet.toTop.map p) b,
      SSet.toTop.map i ≫ c = a :=
  weaklyContractible_realized_extension _ (kan_acyclic_simplex_continuousFiber_weak n p hp b) i a

/-- For a finite parameter complex, the exact fibre extension takes place
in one finite subcomplex of the ORIGINAL total space, with constant base
coordinate at every point and the whole continuous boundary retained. -/
theorem finite_acyclic_simplex_continuousFiber_extension {E A K : SSet.{0}} [K.Finite]
    (n : ℕ) (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (Δ[n] : SSet.{0}))
    (i : A ⟶ K) [Mono i]
    (a : SSet.toTop.obj A ⟶ continuousFiber (SSet.toTop.map p) b) :
    ∃ (S : E.Subcomplex) (_ : SSet.Finite S.toSSet)
      (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
      SSet.toTop.map i ≫ c ≫ SSet.toTop.map S.ι =
        a ≫ continuousFiberInclusion (SSet.toTop.map p) b ∧
      ∀ z, (SSet.toTop.map p).hom ((SSet.toTop.map S.ι).hom (c.hom z)) = b := by
  obtain ⟨g, hg⟩ := kan_acyclic_simplex_continuousFiber_extension n p hp b i a
  let f := g ≫ continuousFiberInclusion (SSet.toTop.map p) b
  have : CompactSpace (SSet.toTop.obj K) := RealizationPrism.compactSpace_of_finite K
  obtain ⟨S, hS, c, hc⟩ := RealizationPrism.compact_map_factors E f.hom
  refine ⟨S, hS, TopCat.ofHom c, ?_, ?_⟩
  · have hc' : TopCat.ofHom c ≫ SSet.toTop.map S.ι = f := by
      apply TopCat.hom_ext
      exact hc
    rw [hc']
    exact congrArg (fun k => k ≫ continuousFiberInclusion (SSet.toTop.map p) b) hg
  · intro z
    have he := congrArg (fun h => h z) hc
    change (SSet.toTop.map S.ι).hom (c z) = (g.hom z).val at he
    change (SSet.toTop.map p).hom ((SSet.toTop.map S.ι).hom (c z)) = b
    rw [he]
    exact (g.hom z).property

end

end Thomason.Construction

end

section

/-! # Exact finite continuous extensions in all fibres over a cube -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Every literal point fibre of an acyclic Kan map over a cube is
weakly contractible, including fibres over nonvertex points. -/
theorem kan_acyclic_cube_continuousFiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (obj n)) :
    IsWeakHomotopyEquivalence (ContinuousMap.const (continuousFiber (SSet.toTop.map p) b) ()) :=
  (kan_cube_allPointFiberComparison_weak n p b).comp
    (continuousHomotopyFiber_weak (SSet.toTop.map p) hp b)

/-- Higher continuous boundary families extend EXACTLY inside a literal
fibre of an acyclic Kan cube map. This is a geometric extension and
does not claim a simplicial filler. -/
theorem kan_acyclic_cube_continuousFiber_extension {E A K : SSet.{0}} (n : ℕ)
    (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (obj n))
    (i : A ⟶ K) [Mono i]
    (a : SSet.toTop.obj A ⟶ continuousFiber (SSet.toTop.map p) b) :
    ∃ c : SSet.toTop.obj K ⟶ continuousFiber (SSet.toTop.map p) b,
      SSet.toTop.map i ≫ c = a :=
  weaklyContractible_realized_extension _ (kan_acyclic_cube_continuousFiber_weak n p hp b) i a

/-- For a finite parameter complex, the exact fibre extension takes place
in one finite subcomplex of the ORIGINAL total space, with constant base
coordinate at every point and the whole continuous boundary retained. -/
theorem finite_acyclic_cube_continuousFiber_extension {E A K : SSet.{0}} [K.Finite]
    (n : ℕ) (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj (obj n))
    (i : A ⟶ K) [Mono i]
    (a : SSet.toTop.obj A ⟶ continuousFiber (SSet.toTop.map p) b) :
    ∃ (S : E.Subcomplex) (_ : SSet.Finite S.toSSet)
      (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
      SSet.toTop.map i ≫ c ≫ SSet.toTop.map S.ι =
        a ≫ continuousFiberInclusion (SSet.toTop.map p) b ∧
      ∀ z, (SSet.toTop.map p).hom ((SSet.toTop.map S.ι).hom (c.hom z)) = b := by
  obtain ⟨g, hg⟩ := kan_acyclic_cube_continuousFiber_extension n p hp b i a
  let f := g ≫ continuousFiberInclusion (SSet.toTop.map p) b
  have : CompactSpace (SSet.toTop.obj K) := RealizationPrism.compactSpace_of_finite K
  obtain ⟨S, hS, c, hc⟩ := RealizationPrism.compact_map_factors E f.hom
  refine ⟨S, hS, TopCat.ofHom c, ?_, ?_⟩
  · have hc' : TopCat.ofHom c ≫ SSet.toTop.map S.ι = f := by
      apply TopCat.hom_ext
      exact hc
    rw [hc']
    exact congrArg (fun k => k ≫ continuousFiberInclusion (SSet.toTop.map p) b) hg
  · intro z
    have he := congrArg (fun h => h z) hc
    change (SSet.toTop.map S.ι).hom (c z) = (g.hom z).val at he
    change (SSet.toTop.map p).hom ((SSet.toTop.map S.ι).hom (c z)) = b
    rw [he]
    exact (g.hom z).property

end

end Thomason.Construction.RealizedCube

end

section

/-! # Relative homotopy lifting through actual weak equivalences -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- Every actual weak equivalence lifts a square on a realized simplicial
mono up to a target homotopy. The source boundary extension is exact and
the target homotopy fixes the entire realized subcomplex pointwise. -/
theorem weak_relative_realization_lift {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f.hom) {K L : SSet.{0}} (i : K ⟶ L) [Mono i]
    (a : SSet.toTop.obj K ⟶ X) (b : SSet.toTop.obj L ⟶ Y)
    (h : a ≫ f = SSet.toTop.map i ≫ b) :
    ∃ c : SSet.toTop.obj L ⟶ X,
      SSet.toTop.map i ≫ c = a ∧
      Nonempty ((c ≫ f).hom.HomotopyRel b.hom (Set.range (SSet.toTop.map i).hom)) := by
  let q := mappingPathProjection f
  let j := mappingPathInclusion f
  let r := mappingPathRetraction f
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map q) := mappingPath_singular_fibration f
  have hq : IsWeakHomotopyEquivalence q.hom := (mappingPathProjection_weak_iff f).mpr hf
  let : HasLiftingProperty (SSet.toTop.map i) q :=
    singular_fibration_realization_mono_lifting q hq i
  let sq : CommSq (a ≫ j) (SSet.toTop.map i) q b := ⟨by
    change (a ≫ mappingPathInclusion f) ≫ mappingPathProjection f = _
    rw [Category.assoc, mappingPath_factorization]
    exact h⟩
  let c := sq.lift ≫ r
  have hc : SSet.toTop.map i ≫ c = a := by
    dsimp [c]
    rw [← Category.assoc, sq.fac_left, Category.assoc]
    rfl
  refine ⟨c, hc, ⟨{
    toFun := fun z => (sq.lift.hom z.2).val.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left := fun x => (sq.lift.hom x).property
    map_one_left := fun x => congrArg (fun t => t.hom x) sq.fac_right
    prop' := ?_ }⟩⟩
  intro t x hx
  obtain ⟨z, rfl⟩ := hx
  have he : sq.lift.hom ((SSet.toTop.map i).hom z) = j.hom (a.hom z) :=
    congrArg (fun u => u.hom z) sq.fac_left
  change (sq.lift.hom ((SSet.toTop.map i).hom z)).val.2 t = _
  rw [he]
  exact (congrArg (fun u => f.hom (u.hom z)) hc).symm

end

end Thomason.Construction

end

section

/-! # Finite relative approximation along actual realization comparisons -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- Relative lifting along an actual weak map with realization source can
be performed in one finite simplicial subcomplex. The prescribed simplicial
boundary map factors through that same subcomplex exactly. -/
theorem finite_relative_realization_lift {A B L : SSet.{0}} [B.Finite]
    (i : A ⟶ B) [Mono i] {Y : TopCat.{0}} (f : SSet.toTop.obj L ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f.hom) (a : A ⟶ L)
    (b : SSet.toTop.obj B ⟶ Y) (h : SSet.toTop.map a ≫ f = SSet.toTop.map i ≫ b) :
    ∃ S : L.Subcomplex, SSet.Finite (S : SSet) ∧
      ∃ (a' : A ⟶ (S : SSet)) (c : SSet.toTop.obj B ⟶ SSet.toTop.obj (S : SSet)),
        a' ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        Nonempty ((c ≫ SSet.toTop.map S.ι ≫ f).hom.HomotopyRel b.hom
          (Set.range (SSet.toTop.map i).hom)) := by
  let : CompactSpace (SSet.toTop.obj B) := RealizationPrism.compactSpace_of_finite B
  obtain ⟨c, hc, hH⟩ := weak_relative_realization_lift f hf i (SSet.toTop.map a) b h
  obtain ⟨T, hT, cT, hcT⟩ := RealizationPrism.compact_map_factors L c.hom
  let : A.Finite := SSet.finite_of_mono i
  let : SSet.Finite (T : SSet) := hT
  let S : L.Subcomplex := T ⊔ SSet.Subcomplex.range a
  have hS : SSet.Finite (S : SSet) := by
    let U : Bool → L.Subcomplex := fun v => if v then T else SSet.Subcomplex.range a
    have he : S = iSup U := by
      apply le_antisymm
      · apply sup_le
        · exact le_iSup U true
        · exact le_iSup U false
      · apply iSup_le
        intro v
        cases v
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff U).mpr
    intro v
    cases v <;> dsimp [U] <;> infer_instance
  let j : (T : SSet) ⟶ (S : SSet) := SSet.Subcomplex.homOfLE le_sup_left
  let a' : A ⟶ (S : SSet) := S.lift a le_sup_right
  let c' : SSet.toTop.obj B ⟶ SSet.toTop.obj (S : SSet) := TopCat.ofHom cT ≫ SSet.toTop.map j
  have ha' : a' ≫ S.ι = a := rfl
  have hj : j ≫ S.ι = T.ι := rfl
  have hc' : c' ≫ SSet.toTop.map S.ι = c := by
    dsimp only [c']
    rw [Category.assoc, ← SSet.toTop.map_comp, hj]
    apply TopCat.hom_ext
    exact hcT
  refine ⟨S, hS, a', c', ha', ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply RealizationPrism.inclusion_injective L S
    have e := congrArg (fun g => g.hom z)
      (show (SSet.toTop.map i ≫ c') ≫ SSet.toTop.map S.ι =
          SSet.toTop.map a' ≫ SSet.toTop.map S.ι by
        rw [Category.assoc, hc', hc, ← SSet.toTop.map_comp, ha'])
    exact e
  · rw [← Category.assoc, hc']
    exact hH

/-- A continuous family of paths in a Kan realization admits a relative
finite approximation by realized internal paths. The homotopy is fixed on
the prescribed simplicial parameter subcomplex. No claim about fixed
endpoint fibres is hidden in this statement. -/
theorem finite_relative_internalPath_approximation {A B X : SSet.{0}} [B.Finite]
    [SSet.KanComplex X] (i : A ⟶ B) [Mono i]
    (a : A ⟶ internalPathObject X)
    (b : SSet.toTop.obj B ⟶ continuousPathSpace (SSet.toTop.obj X))
    (h : SSet.toTop.map a ≫ realizedInternalPathComparison X = SSet.toTop.map i ≫ b) :
    ∃ S : (internalPathObject X).Subcomplex, SSet.Finite (S : SSet) ∧
      ∃ (a' : A ⟶ (S : SSet)) (c : SSet.toTop.obj B ⟶ SSet.toTop.obj (S : SSet)),
        a' ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        Nonempty ((c ≫ SSet.toTop.map S.ι ≫ realizedInternalPathComparison X).hom.HomotopyRel
          b.hom (Set.range (SSet.toTop.map i).hom)) :=
  finite_relative_realization_lift i (realizedInternalPathComparison X)
    (realizedInternalPathComparison_weak X) a b h

end

end Thomason.Construction

end

end OAI
