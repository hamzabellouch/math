import OAI.CategoryTheory.Thomason.Chains.NerveFaceChains
import OAI.CategoryTheory.Thomason.Simplicial.AcyclicKanSimplexLifting
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSortedCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionKan
import OAI.CategoryTheory.Thomason.Simplicial.KanFinitePosetExtension
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.SubcomplexFaceLifting
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace OAI

section

/-! # Relative finite approximation of weak Kan lifts

The actual continuous lift is resolved in a finite nonsingular target.
Relative approximation retains its comparison class, so Kan lifting makes
its projection exact before relative subdivision descent.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open SubdivisionBarycentric NonsingularLastVertex
open SSet.modelCategoryQuillen

noncomputable section

private theorem iteratedChainPoset_nonempty (P : PartOrd.{0}) [Nonempty P] (r : ℕ) :
    Nonempty (iteratedChainPoset P r) := by
  classical
  induction r with
  | zero => exact inferInstanceAs (Nonempty P)
  | succ r ih =>
    obtain ⟨p⟩ := ih
    exact ⟨{ finset := {p}
             nonempty := Finset.singleton_nonempty p
             comparable := by
               rintro ⟨x, hx⟩ ⟨y, hy⟩
               simp only [Finset.mem_singleton] at hx hy
               apply Or.inl
               change x ≤ y
               exact le_of_eq (hx.trans hy.symm) }⟩

theorem weak_kan_lift_on_resolved_facePoset {A B E Z : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite]
    [SSet.KanComplex E] [SSet.KanComplex Z]
    (i : nerve A.N ⟶ B) [Mono i]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (a : A ⟶ E) (b : B ⟶ Z)
    (ha : (map A ≫ a) ≫ p = i ≫ b)
    (c : SSet.toTop.obj B ⟶ SSet.toTop.obj E)
    (hc : SSet.toTop.map i ≫ c = SSet.toTop.map (map A ≫ a))
    (H : (c ≫ SSet.toTop.map p).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map i).hom)) :
    ∃ d : nerve B.N ⟶ E,
      nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor ≫ d =
        map (nerve A.N) ≫ map A ≫ a ∧
      d ≫ p = map B ≫ b := by
  classical
  let j := nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor
  let : Mono j := faceMap_nerve_mono i
  rcases isEmpty_or_nonempty B.N with hB | hB
  · have h0 : Limits.IsInitial (nerve B.N) := SSet.isInitialOfNotNonempty (by
      rintro ⟨s⟩
      exact isEmptyElim (s.obj 0))
    have h1 : Limits.IsInitial (nerve (nerve A.N).N) := SSet.isInitialOfNotNonempty (by
      rintro ⟨s⟩
      exact isEmptyElim (faceMap i (preservesNondegenerate_of_mono i) (s.obj 0)))
    exact ⟨h0.to E, h1.hom_ext _ _, h0.hom_ext _ _⟩
  let : (nerve A.N).Finite := SSet.finite_of_mono i
  obtain ⟨S, hS, a', ha', c', _, hc', he, ⟨HR⟩⟩ :=
    FaceSimplexResolution.finite_relative_order_lift_with_comparison i a c hc.symm
  let : SSet.Finite S.toSSet := hS
  let : Fintype B.N := Fintype.ofFinite _
  let g := faceMap a' ha'
  let k : nerve S.toSSet.N ⟶ E :=
    map S.toSSet ≫ S.ι ≫ FaceSimplexResolution.augmentation E
  let b0 : nerve B.N ⟶ Z := map B ≫ b
  have hj : j ≫ map B = map (nerve A.N) ≫ i :=
    map_naturality i (preservesNondegenerate_of_mono i)
  have hboundary : (nerveMap g.monotone.functor ≫ k) ≫ p = j ≫ b0 := by
    rw [he]
    calc
      (map (nerve A.N) ≫ map A ≫ a) ≫ p =
          map (nerve A.N) ≫ ((map A ≫ a) ≫ p) := by simp only [Category.assoc]
      _ = map (nerve A.N) ≫ (i ≫ b) := congrArg (map (nerve A.N) ≫ ·) ha
      _ = j ≫ b0 := by rw [← Category.assoc, ← hj, Category.assoc]
  have himage (x : SSet.toTop.obj (nerve B.N))
      (hx : x ∈ Set.range (SSet.toTop.map j).hom) :
      (SSet.toTop.map (map B)).hom x ∈ Set.range (SSet.toTop.map i).hom := by
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(SSet.toTop.map (map (nerve A.N))).hom z, ?_⟩
    have hz := congrArg (fun q => (SSet.toTop.map q).hom z) hj
    simp only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] at hz
    exact hz.symm
  let HR' : ((SSet.toTop.map k).hom.comp c'.hom).HomotopyRel
      (SSet.toTop.map (map B) ≫ c).hom (Set.range (SSet.toTop.map j).hom) :=
    HR.cast (by simp only [k, SSet.toTop.map_comp, TopCat.hom_comp]) rfl
  let H' : (SSet.toTop.map (map B) ≫ c ≫ SSet.toTop.map p).hom.HomotopyRel
      (SSet.toTop.map b0).hom (Set.range (SSet.toTop.map j).hom) := {
    toHomotopy := (H.toHomotopy.comp
      (ContinuousMap.Homotopy.refl (SSet.toTop.map (map B)).hom)).cast rfl
        (by dsimp only [b0]; rw [SSet.toTop.map_comp]; rfl)
    prop' := by
      intro t x hx
      exact H.prop t _ (himage x hx) }
  let T := (HR'.compContinuousMap (SSet.toTop.map p).hom).trans H'
  obtain ⟨r, d, hd, ⟨HD⟩⟩ := exists_relative_kan_approximation
    (PartOrd.of (nerve A.N).N) (PartOrd.of B.N)
    (faceMap i (preservesNondegenerate_of_mono i)) (faceMap_injective i)
    g c'.hom (fun z => congrArg (fun f => f.hom z) hc') k
  let ir := (iteratedSubdivision r).map j
  have hir : Mono ir := iteratedSubdivision_mono r j
  let L := iteratedLastVertex (nerve B.N) r
  have hnat : ir ≫ L = iteratedLastVertex (nerve (nerve A.N).N) r ≫ j :=
    iteratedLastVertex_naturality j r
  have hirange (x : SSet.toTop.obj ((iteratedSubdivision r).obj (nerve B.N)))
      (hx : x ∈ Set.range (SSet.toTop.map ir).hom) :
      (SSet.toTop.map L).hom x ∈ Set.range (SSet.toTop.map j).hom := by
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(SSet.toTop.map (iteratedLastVertex (nerve (nerve A.N).N) r)).hom z, ?_⟩
    have hz := congrArg (fun q => (SSet.toTop.map q).hom z) hnat
    simp only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] at hz
    exact hz.symm
  let TL : (((SSet.toTop.map p).hom.comp
      ((SSet.toTop.map k).hom.comp c'.hom)).comp (SSet.toTop.map L).hom).HomotopyRel
      ((SSet.toTop.map b0).hom.comp (SSet.toTop.map L).hom)
      (Set.range (SSet.toTop.map ir).hom) := by
    -- The following explicit record only changes the stationary set.
    exact {
      toHomotopy := T.toHomotopy.comp
        (ContinuousMap.Homotopy.refl (SSet.toTop.map L).hom)
      prop' := fun t x hx => T.prop t _ (hirange x hx) }
  let Q := (HD.symm.compContinuousMap (SSet.toTop.map p).hom).trans TL
  have HQ : (SSet.toTop.map (d ≫ p)).hom.HomotopyRel
      (SSet.toTop.map (L ≫ b0)).hom (Set.range (SSet.toTop.map ir).hom) :=
    Q.cast (by rw [SSet.toTop.map_comp]; rfl)
      (congrArg TopCat.Hom.hom (SSet.toTop.map_comp L b0).symm)
  have hdb : ir ≫ (d ≫ p) = ir ≫ (L ≫ b0) := by
    calc
      ir ≫ (d ≫ p) = (ir ≫ d) ≫ p := (Category.assoc _ _ _).symm
      _ = (iteratedLastVertex (nerve (nerve A.N).N) r ≫
          nerveMap g.monotone.functor ≫ k) ≫ p := by rw [hd]
      _ = iteratedLastVertex (nerve (nerve A.N).N) r ≫ (j ≫ b0) := by
        simpa only [Category.assoc] using congrArg
          (iteratedLastVertex (nerve (nerve A.N).N) r ≫ ·) hboundary
      _ = ir ≫ (L ≫ b0) := by rw [← Category.assoc, ← hnat, Category.assoc]
  let P := PartOrd.of B.N
  let : Nonempty (iteratedChainPoset P r) := iteratedChainPoset_nonempty P r
  obtain ⟨m, e, hem⟩ := finitePoset_nerve_simplex_embedding (iteratedChainPoset P r)
  let er := (iteratedSubdivisionNerveIso P r).hom ≫ e
  have : Mono er := inferInstance
  obtain ⟨l, hl, hlp⟩ := exactify_realization_relative_lift_mono er ir p d (L ≫ b0) hdb HQ
  have hla : ir ≫ l = iteratedLastVertex (nerve (nerve A.N).N) r ≫
      (map (nerve A.N) ≫ map A ≫ a) := by
    rw [hl, hd]
    exact congrArg (iteratedLastVertex (nerve (nerve A.N).N) r ≫ ·) he
  exact exists_iteratedSubdivision_relative_base_descent j p
    (iteratedSubdivision_canonical_anodyne (PartOrd.of (nerve A.N).N))
    (iteratedSubdivision_canonical_anodyne P) r (map (nerve A.N) ≫ map A ≫ a)
    l b0 (by rw [← he]; exact hboundary) hlp hla

end

end Thomason.Construction

end

section

/-! # Weak Kan lifts on finite nonsingular face posets

A relative continuous lift through the actual weak equivalence is resolved
to a finite face-poset lift. The exact base equation is retained while the
one remaining subdivision is removed.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open SSet.modelCategoryQuillen

noncomputable section

theorem weak_kan_lift_on_facePoset {A B E Z : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite]
    [SSet.KanComplex E] [SSet.KanComplex Z]
    (i : A ⟶ B) [Mono i] (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (a : A ⟶ E) (b : B ⟶ Z)
    (ha : a ≫ p = i ≫ b) :
    ∃ d : nerve B.N ⟶ E,
      nerveMap (NonsingularLastVertex.faceMap i
        (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor ≫ d =
        NonsingularLastVertex.map A ≫ a ∧
      d ≫ p = NonsingularLastVertex.map B ≫ b := by
  let : A.Finite := SSet.finite_of_mono i
  let : (nerve B.N).Finite := PosetGeometry.nerve_finite B.N
  let j := nerveMap (NonsingularLastVertex.faceMap i
    (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor
  let : Mono j := NonsingularLastVertex.faceMap_nerve_mono i
  let b' := NonsingularLastVertex.map B ≫ b
  have ha' : (NonsingularLastVertex.map A ≫ a) ≫ p = j ≫ b' := by
    rw [Category.assoc, ha, ← Category.assoc,
      ← NonsingularLastVertex.map_naturality i
        (NonsingularLastVertex.preservesNondegenerate_of_mono i), Category.assoc]
  have hs : SSet.toTop.map (NonsingularLastVertex.map A ≫ a) ≫ SSet.toTop.map p =
      SSet.toTop.map j ≫ SSet.toTop.map b' := by
    rw [← SSet.toTop.map_comp, ha', SSet.toTop.map_comp]
  obtain ⟨c, hc, ⟨H⟩⟩ := weak_relative_realization_lift (SSet.toTop.map p) hp j
    (SSet.toTop.map (NonsingularLastVertex.map A ≫ a)) (SSet.toTop.map b') hs
  obtain ⟨d, hd, hdp⟩ := weak_kan_lift_on_resolved_facePoset j p a b' ha' c hc H
  let f := (NerveFaceChains.subdivisionIso B.N).hom ≫ d
  have hf : SSet.sd.map j ≫ f = lastVertex.app (nerve A.N) ≫
      (NonsingularLastVertex.map A ≫ a) := by
    change SSet.sd.map j ≫ ((NerveFaceChains.subdivisionIso B.N).hom ≫ d) = _
    rw [← Category.assoc, NerveFaceChains.subdivisionIso_naturality
      (NonsingularLastVertex.faceMap i (NonsingularLastVertex.preservesNondegenerate_of_mono i))
      (NonsingularLastVertex.preservesNondegenerate_of_mono j),
      Category.assoc, hd, ← Category.assoc, NerveFaceChains.subdivisionIso_lastVertex]
  have hfp : f ≫ p = lastVertex.app (nerve B.N) ≫ b' := by
    change ((NerveFaceChains.subdivisionIso B.N).hom ≫ d) ≫ p = _
    rw [Category.assoc, hdp, ← Category.assoc, NerveFaceChains.subdivisionIso_lastVertex]
  obtain ⟨e, _, he, hep, _, _⟩ := exists_subdivision_relative_base_descent j p
    (canonicalExtension_finitePoset_anodyne A.N) (canonicalExtension_finitePoset_anodyne B.N)
    (canonicalExtension_subdivision_finitePoset_anodyne A.N)
    (canonicalExtension_subdivision_finitePoset_anodyne B.N)
    (NonsingularLastVertex.map A ≫ a) f b' ha' hfp hf
  exact ⟨e, he, hep⟩

end

end Thomason.Construction

end

section

/-! # Acyclic lifting for the actual Kan weak-equivalence class

The finite relative realization comparison gives exact face-poset lifts.
The proved first-subdivision comparison returns them to the original
simplex boundaries. Infinite extension then removes the fibrancy
assumptions on the source and base of the original Kan fibration.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem weak_kan_lift_simplexSubcomplex {n : ℕ}
    (A B : (Δ[n] : SSet.{0}).Subcomplex) (hAB : A ≤ B)
    {E Z : SSet.{0}} [SSet.KanComplex E] [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p)
    (a : A.toSSet ⟶ E) (b : B.toSSet ⟶ Z)
    (ha : a ≫ p = SSet.Subcomplex.homOfLE hAB ≫ b) :
    ∃ g : B.toSSet ⟶ E,
      SSet.Subcomplex.homOfLE hAB ≫ g = a ∧ g ≫ p = b := by
  obtain ⟨d, hd, hdp⟩ := weak_kan_lift_on_facePoset
    (SSet.Subcomplex.homOfLE hAB) p hp a b ha
  exact simplexSubcomplex_lift_of_facePoset_lift A B hAB p a b ha d hd hdp

theorem weak_kan_boundary_lifting {E Z : SSet.{0}}
    [SSet.KanComplex E] [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι p := by
  refine ⟨fun {a b} sq => ?_⟩
  let T : (Δ[n] : SSet.{0}).Subcomplex := ⊤
  let e := SSet.Subcomplex.topIso (Δ[n] : SSet.{0})
  let i : (SSet.boundary n : SSet.{0}) ⟶ T.toSSet := SSet.Subcomplex.homOfLE le_top
  have hi : i ≫ e.hom = (SSet.boundary n).ι := rfl
  have ha : a ≫ p = i ≫ (e.hom ≫ b) := by
    rw [← Category.assoc, hi]
    exact sq.w
  obtain ⟨d, hd, hdp⟩ := weak_kan_lift_simplexSubcomplex
    (SSet.boundary n) T le_top p hp a (e.hom ≫ b) ha
  refine ⟨⟨{ l := e.inv ≫ d, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← hi]
    exact (Category.assoc _ _ _).trans
      ((congrArg (i ≫ ·) (e.hom_inv_id_assoc d)).trans hd)
  · rw [Category.assoc, hdp, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem weak_kan_boundary_rlp {E Z : SSet.{0}}
    [SSet.KanComplex E] [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) : I.rlp p := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact weak_kan_boundary_lifting p hp n

/-- Every Kan fibration which is an actual realization weak equivalence
lifts against every boundary inclusion, in every dimension. -/
theorem acyclicKanLifting_unconditional : PublishedAcyclicKanLifting :=
  InfiniteExtension.acyclicKanLifting_of_fibrant_case
    (fun {_ _} _ _ p _ hp => weak_kan_boundary_rlp p hp)

end

end Thomason.Construction

end

section

/-! # Realization weak equivalences are closed under filtered colimits

For Kan complexes, the genuine mapping-path projection is a weak
equivalence precisely when it has boundary lifting. Mapping paths commute
with filtered colimits, and every finite boundary lifting square occurs at
a stage. The actual extension-to-infinity functor then removes the Kan
hypotheses.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

variable {K : Type} [Category.{0} K] [IsFiltered K]
    {D E : K ⥤ SSet.{0}}

theorem kan_filtered_colimMap_weak (η : D ⟶ E)
    (hD : ∀ j, SSet.KanComplex (D.obj j))
    (hE : ∀ j, SSet.KanComplex (E.obj j))
    (hη : ∀ j, realizationWeakEquivalences (η.app j)) :
    realizationWeakEquivalences (colimMap η) := by
  let q := SimplicialMappingPathDiagram.endpoint η
  have hq : I.rlp (colimMap q) := by
    apply filtered_colimit_boundary_rlp (colimit.isColimit _) (colimit.isColimit _)
      q (colimMap q) (ι_colimMap q)
    intro j
    let : SSet.KanComplex (D.obj j) := hD j
    let : SSet.KanComplex (E.obj j) := hE j
    change I.rlp (simplicialMappingPathProjection (η.app j))
    have := simplicialMappingPath_projection_fibration (η.app j)
    exact acyclicKanLifting_unconditional _
      ⟨(fibration_iff _).mp inferInstance,
        (simplicialMappingPath_projection_weak_iff (η.app j)).mpr (hη j)⟩
  have hw : realizationWeakEquivalences
      ((SimplicialMappingPathDiagram.comparison η).hom ≫
        simplicialMappingPathProjection (colimMap η)) := by
    rw [SimplicialMappingPathDiagram.comparison_projection]
    exact boundary_rlp_weak _ hq
  apply (simplicialMappingPath_projection_weak_iff_unconditional (colimMap η)).mp
  exact realizationWeakEquivalences.of_precomp _ _
    (realizationWeakEquivalences.of_isIso _) hw

theorem realization_filtered_colimMap_weak (η : D ⟶ E)
    (hη : ∀ j, realizationWeakEquivalences (η.app j)) :
    realizationWeakEquivalences (colimMap η) := by
  let F := InfiniteExtension.functor
  have hw : realizationWeakEquivalences (colimMap (Functor.whiskerRight η F)) :=
    kan_filtered_colimMap_weak (Functor.whiskerRight η F)
      (fun j => InfiniteExtension.kan (D.obj j))
      (fun j => InfiniteExtension.kan (E.obj j))
      (fun j => (InfiniteExtension.map_weak_iff (η.app j)).mpr (hη j))
  have hn := (preservesColimitNatIso F).hom.naturality η
  change F.map (colimMap η) ≫ (preservesColimitIso F E).hom =
    (preservesColimitIso F D).hom ≫ colimMap (Functor.whiskerRight η F) at hn
  apply (InfiniteExtension.map_weak_iff (colimMap η)).mp
  apply realizationWeakEquivalences.of_postcomp _ (preservesColimitIso F E).hom
    (realizationWeakEquivalences.of_isIso _)
  change realizationWeakEquivalences (F.map (colimMap η) ≫
    (preservesColimitIso F E).hom)
  rw [hn]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) hw

/-- The result for arbitrary chosen colimit cocones, retaining the given
comparison map rather than replacing it by the canonical colimit map. -/
theorem realization_filtered_colimit_weak {c : Cocone D} {d : Cocone E}
    (hc : IsColimit c) (hd : IsColimit d) (η : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = η.app j ≫ d.ι.app j)
    (hη : ∀ j, realizationWeakEquivalences (η.app j)) :
    realizationWeakEquivalences p := by
  let eD := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  let eE := hd.coconePointUniqueUpToIso (colimit.isColimit E)
  have he : p ≫ eE.hom = eD.hom ≫ colimMap η := by
    apply hc.hom_ext
    intro j
    dsimp only [eD, eE]
    rw [← Category.assoc, hp j, Category.assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom,
      ← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (ι_colimMap η j).symm
  apply realizationWeakEquivalences.of_postcomp p eE.hom
    (realizationWeakEquivalences.of_isIso _)
  rw [he]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (realization_filtered_colimMap_weak η hη)

instance realizationWeakEquivalences_stableUnderFilteredColimits :
    realizationWeakEquivalences.{0}.IsStableUnderFilteredColimits.{0,0} where
  isStableUnderColimitsOfShape _ :=
    ⟨fun _ _ _ _ hc hd η hη p hp => realization_filtered_colimit_weak hc hd η p hp hη⟩

end

end Thomason.Construction

end

section

/-! # Weak components of a natural transformation and filtered colimits

The statements keep the actual component of the natural transformation at
the chosen colimit. They therefore apply directly to adjunction units,
without replacing them by unspecified comparison morphisms.
-/

namespace Thomason.Construction.WeakNaturalTransformationColimits

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

section General

variable {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty D) {F G : C ⥤ D} (η : F ⟶ G)

/-- Weakness of a component propagates across any map whose two functorial
images are weak equivalences. -/
theorem app_weak_iff_of_weak_images [W.HasTwoOutOfThreeProperty]
    {X Y : C} (f : X ⟶ Y) (hF : W (F.map f)) (hG : W (G.map f)) :
    W (η.app X) ↔ W (η.app Y) := by
  constructor
  · intro hX
    apply W.of_precomp (F.map f) (η.app Y) hF
    rw [η.naturality]
    exact W.comp_mem _ _ hX hG
  · intro hY
    apply W.of_postcomp (η.app X) (G.map f) hG
    rw [← η.naturality]
    exact W.comp_mem _ _ hF hY

/-- A natural transformation that is weak on a diagram is weak at its
chosen colimit when both functors preserve that colimit. -/
theorem app_weak_of_isColimit
    {J : Type u₃} [Category.{v₃} J] [W.IsStableUnderColimitsOfShape J]
    {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K F] [PreservesColimit K G]
    (hη : ∀ j, W (η.app (K.obj j))) : W (η.app c.pt) := by
  refine MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := W) (K ⋙ F) (K ⋙ G) (F.mapCocone c) (G.mapCocone c)
    (isColimitOfPreserves F hc) (isColimitOfPreserves G hc)
    (Functor.whiskerLeft K η) hη (η.app c.pt) ?_
  intro j
  exact η.naturality (c.ι.app j)

/-- The canonical colimit specialization retains exactly the given component. -/
theorem app_weak_colimit
    {J : Type u₃} [Category.{v₃} J] [W.IsStableUnderColimitsOfShape J]
    (K : J ⥤ C) [HasColimit K]
    [PreservesColimit K F] [PreservesColimit K G]
    (hη : ∀ j, W (η.app (K.obj j))) : W (η.app (colimit K)) :=
  app_weak_of_isColimit W η (colimit.isColimit K) hη

end General

section Realization

variable {C : Type u₁} [Category.{v₁} C]
    {F G : C ⥤ SSet.{0}} (η : F ⟶ G)

/-- The actual realization weak-equivalence test passes from every object
of a filtered diagram to its chosen colimit. -/
theorem realization_app_weak_of_isColimit
    {J : Type} [Category.{0} J] [IsFiltered J]
    {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K F] [PreservesColimit K G]
    (hη : ∀ j, realizationWeakEquivalences (η.app (K.obj j))) :
    realizationWeakEquivalences (η.app c.pt) :=
  app_weak_of_isColimit realizationWeakEquivalences η hc hη

/-- In particular this applies to each literal component of an adjunction unit. -/
theorem realization_unit_weak_of_isColimit
    {L : SSet.{0} ⥤ C} {R : C ⥤ SSet.{0}} (adj : L ⊣ R)
    {J : Type} [Category.{0} J] [IsFiltered J]
    {K : J ⥤ SSet.{0}} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K (L ⋙ R)]
    (hη : ∀ j, realizationWeakEquivalences (adj.unit.app (K.obj j))) :
    realizationWeakEquivalences (adj.unit.app c.pt) :=
  realization_app_weak_of_isColimit adj.unit hc hη

end Realization

end Thomason.Construction.WeakNaturalTransformationColimits

end

section

/-! # Reduction of weak units to finite poset nerves

The reduction uses the actual nonsingular face-simplex resolution and its
proved augmentation equivalence. It applies once the target endofunctor
preserves realization weak equivalences and filtered colimits.
-/

namespace Thomason.Construction.FinitePosetUnitReduction

open CategoryTheory CategoryTheory.Limits
open WeakNaturalTransformationColimits

noncomputable section

variable {F : SSet.{0} ⥤ SSet.{0}} (η : 𝟭 SSet.{0} ⟶ F)
    (hF : ∀ {X Y : SSet.{0}} (f : X ⟶ Y),
      realizationWeakEquivalences f → realizationWeakEquivalences (F.map f))
    (hP : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (η.app (nerve P)))

include hF hP in
/-- Finite nonsingular simplicial sets reduce to their actual finite
nondegenerate face posets. -/
theorem finite_nonsingular (X : SSet.{0}) [X.Finite] [X.Nonsingular] :
    realizationWeakEquivalences (η.app X) := by
  have hw := NonsingularLastVertex.map_weak X
  exact (app_weak_iff_of_weak_images realizationWeakEquivalences η
    (NonsingularLastVertex.map X) hw (hF _ hw)).mp (hP X.N)

include hF hP in
/-- The filtered union of finite subcomplexes removes the finiteness condition. -/
theorem nonsingular [PreservesFilteredColimitsOfSize.{0,0} F]
    (X : SSet.{0}) [X.Nonsingular] :
    realizationWeakEquivalences (η.app X) := by
  apply realization_app_weak_of_isColimit η (FiniteSimplicialExhaustion.isColimit X)
  intro j
  change realizationWeakEquivalences
    (η.app (FiniteSimplicialExhaustion.support X j).toSSet)
  exact finite_nonsingular η hF hP _

include hF hP in
/-- Weak components on finite poset nerves imply weak components everywhere,
using the proved face-simplex augmentation for arbitrary singular targets. -/
theorem all [PreservesFilteredColimitsOfSize.{0,0} F] (X : SSet.{0}) :
    realizationWeakEquivalences (η.app X) := by
  have hw := FaceSimplexResolution.augmentation_weak X
  exact (app_weak_iff_of_weak_images realizationWeakEquivalences η
    (FaceSimplexResolution.augmentation X) hw (hF _ hw)).mp
    (nonsingular η hF hP _)

end

end Thomason.Construction.FinitePosetUnitReduction

end

end OAI
