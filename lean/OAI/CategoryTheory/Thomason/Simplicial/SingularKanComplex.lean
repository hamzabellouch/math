import OAI.CategoryTheory.Thomason.Gray.TripleGlobeCylinderSource
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

namespace OAI

section

/-! # Uniform finite vertex-star control for maps from cubes -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- Any continuous cube in a realization admits a finite closed grid whose
    individual cell images lie in individual vertex stars. -/
theorem cube_grid_vertexStar_refinement (K : SSet.{0}) (n : ℕ)
    (f : C((Fin n → unitInterval), SSet.toTop.obj K)) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1), ∃ v : K.obj (.op (.mk 0)),
      ∀ x ∈ CubeGrid.cell n m k, f x ∈ vertexStar K v := by
  let U := fun v => f ⁻¹' vertexStar K v
  have hU : ∀ v, IsOpen (U v) := fun v => (vertexStar_isOpen K v).preimage f.continuous
  have hcover : ⋃ v, U v = Set.univ := by
    change (⋃ v, f ⁻¹' vertexStar K v) = Set.univ
    rw [← Set.preimage_iUnion, vertexStar_cover, Set.preimage_univ]
  obtain ⟨ε, hε, hmesh⟩ := CompactSpace.lebesgue_number_lemma U hU hcover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m, fun k => ?_⟩
  obtain ⟨v, hv⟩ := hmesh (CubeGrid.cell n m k) (CubeGrid.cell_nonempty n m k)
    ((CubeGrid.cell_diam n m k).trans hm.le)
  exact ⟨v, hv⟩

/-- The selected star controls positive support in every simplex
    representation of every image point, including degenerate ones. -/
theorem cube_grid_supported_vertex (K : SSet.{0}) (n : ℕ)
    (f : C((Fin n → unitInterval), SSet.toTop.obj K)) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1), ∃ v : K.obj (.op (.mk 0)),
      ∀ x ∈ CubeGrid.cell n m k, ∀ (d : ℕ) (s : K.obj (.op (.mk d)))
        (p : StdSimplex ℝ (Fin (d+1))), simplexPoint K s p = f x →
          ∃ i, 0 < p.weights i ∧ simplexVertex K s i = v := by
  obtain ⟨m, hm⟩ := cube_grid_vertexStar_refinement K n f
  refine ⟨m, fun k => ?_⟩
  obtain ⟨v, hv⟩ := hm k
  refine ⟨v, fun x hx d s p he => ?_⟩
  apply (simplexPoint_mem_vertexStar_iff K s p v).mp
  rw [he]
  exact hv x hx

end

end Thomason.Construction.RealizationPrism

end

section

/-! # The actual realization/product comparison and retracts -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

noncomputable section

/-- The canonical comparison uses the two actual realized projections. -/
def realizationProductComparison (X Y : SSet.{0}) :
    SSet.toTop.obj (X ⊗ Y) ⟶ TopCat.of (SSet.toTop.obj X × SSet.toTop.obj Y) :=
  TopCat.ofHom {
    toFun z := ((SSet.toTop.map (fst X Y)).hom z, (SSet.toTop.map (snd X Y)).hom z)
    continuous_toFun := (SSet.toTop.map (fst X Y)).hom.continuous.prodMk
      (SSet.toTop.map (snd X Y)).hom.continuous }

/-- The right-factor map on the product of actual realizations. -/
def realizationProductRightMap (X : SSet.{0}) {Y Z : SSet.{0}} (f : Y ⟶ Z) :
    TopCat.of (SSet.toTop.obj X × SSet.toTop.obj Y) ⟶
      TopCat.of (SSet.toTop.obj X × SSet.toTop.obj Z) :=
  TopCat.ofHom {
    toFun z := (z.1, (SSet.toTop.map f).hom z.2)
    continuous_toFun := continuous_fst.prodMk ((SSet.toTop.map f).hom.continuous.comp continuous_snd) }

/-- The canonical product comparison is natural in its right factor. -/
theorem realizationProductComparison_naturality_right (X : SSet.{0})
    {Y Z : SSet.{0}} (f : Y ⟶ Z) :
    SSet.toTop.map (X ◁ f) ≫ realizationProductComparison X Z =
      realizationProductComparison X Y ≫ realizationProductRightMap X f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · have h := congrArg (fun k => (SSet.toTop.map k).hom z) (whiskerLeft_fst X f)
    rw [SSet.toTop.map_comp] at h
    exact h
  · have h := congrArg (fun k => (SSet.toTop.map k).hom z) (whiskerLeft_snd X f)
    simp only [SSet.toTop.map_comp] at h
    exact h

theorem realizationProductRightMap_comp (X : SSet.{0}) {Y Z T : SSet.{0}}
    (f : Y ⟶ Z) (g : Z ⟶ T) :
    realizationProductRightMap X (f ≫ g) =
      realizationProductRightMap X f ≫ realizationProductRightMap X g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (z.1, (SSet.toTop.map (f ≫ g)).hom z.2) = _
  rw [SSet.toTop.map_comp]
  rfl

theorem realizationProductRightMap_id (X Y : SSet.{0}) :
    realizationProductRightMap X (𝟙 Y) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (z.1, (SSet.toTop.map (𝟙 Y)).hom z.2) = z
  rw [SSet.toTop.map_id]
  rfl

/-- If the product comparison is an isomorphism for a larger factor, it
is also an isomorphism for any specified simplicial retract. -/
theorem realizationProductComparison_isIso_of_retract (X : SSet.{0})
    {Y Z : SSet.{0}} (i : Y ⟶ Z) (r : Z ⟶ Y) (hir : i ≫ r = 𝟙 Y)
    [IsIso (realizationProductComparison X Z)] :
    IsIso (realizationProductComparison X Y) := by
  let v := realizationProductRightMap X i ≫ inv (realizationProductComparison X Z) ≫
    SSet.toTop.map (X ◁ r)
  have hv₁ : realizationProductComparison X Y ≫ v = 𝟙 _ := by
    dsimp only [v]
    rw [← Category.assoc, ← realizationProductComparison_naturality_right, Category.assoc,
      IsIso.hom_inv_id_assoc, ← SSet.toTop.map_comp, ← whiskerLeft_comp, hir,
      whiskerLeft_id, SSet.toTop.map_id]
  have hv₂ : v ≫ realizationProductComparison X Y = 𝟙 _ := by
    dsimp only [v]
    rw [Category.assoc, Category.assoc, realizationProductComparison_naturality_right,
      ← Category.assoc (inv _), IsIso.inv_hom_id, Category.id_comp,
      ← realizationProductRightMap_comp, hir, realizationProductRightMap_id]
  exact ⟨⟨v, hv₁, hv₂⟩⟩

end

end Thomason.Construction

end

section

/-! # Exact homeomorphisms for realized cubes and their entire boundaries -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The actual cubical section is also a right inverse, in every dimension. -/
theorem section_coordinates (n : ℕ) (x : SSet.toTop.obj (obj n)) :
    sectionMap n (coordinates n x) = x := by
  induction n with
  | zero => exact @Subsingleton.elim (SSet.toTop.obj (Δ[0] : SSet.{0})) inferInstance _ _
  | succ n ih =>
    change (RealizedCylinder.comparison (obj n)).hom
      (sectionMap n (coordinates n ((SSet.toTop.map (CartesianMonoidalCategory.fst
        (obj n) Δ[1])).hom x)),
        PrismBarycentric.realizationTime.hom
          ((SSet.toTop.map (CartesianMonoidalCategory.snd (obj n) Δ[1])).hom x)) = x
    rw [ih]
    exact RealizedCylinder.comparison_coordinates (obj n) x

/-- A finite simplicial cube realizes to the ordinary topological cube,
with the original constructed cubical section as its inverse coordinates. -/
def cubeHomeomorph (n : ℕ) :
    (Fin n → unitInterval) ≃ₜ SSet.toTop.obj (obj n) where
  toFun := sectionMap n
  invFun := coordinates n
  left_inv := coordinates_section n
  right_inv := section_coordinates n
  continuous_toFun := (sectionMap n).continuous
  continuous_invFun := (coordinates n).continuous

/-- The section identifies the entire topological boundary with the actual
realization of the simplicial boundary, not merely a retract of it. -/
theorem boundarySection_coordinates (n : ℕ)
    (x : SSet.toTop.obj (boundary n : SSet.{0})) :
    boundarySection n (boundaryCoordinates n x) = x := by
  apply (RealizationPrism.inclusion_isClosedEmbedding (obj (n+1)) (boundary n)).injective
  rw [boundarySection_inclusion]
  exact section_coordinates (n+1) ((SSet.toTop.map (boundary n).ι).hom x)

/-- The exact boundary homeomorphism is compatible with the ambient cube. -/
def boundaryHomeomorph (n : ℕ) :
    Cube.boundary (Fin (n+1)) ≃ₜ SSet.toTop.obj (boundary n : SSet.{0}) where
  toFun := boundarySection n
  invFun := boundaryCoordinates n
  left_inv := boundaryCoordinates_section n
  right_inv := boundarySection_coordinates n
  continuous_toFun := (boundarySection n).continuous
  continuous_invFun := (boundaryCoordinates n).continuous

/-- An isomorphism of the complete boundary-inclusion arrows. -/
def boundaryArrowIso (n : ℕ) :
    Arrow.mk (boundaryInclusion n) ≅ Arrow.mk (SSet.toTop.map (boundary n).ι) :=
  Arrow.isoMk' _ _ (TopCat.isoOfHomeo (boundaryHomeomorph n))
    (TopCat.isoOfHomeo (cubeHomeomorph (n+1))) (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      exact boundarySection_inclusion n x)

/-- Ordinary cube-boundary lifting and lifting of the corresponding realized
simplicial boundary are exactly equivalent. -/
theorem boundary_lifting_iff {X Y : TopCat.{0}} (p : X ⟶ Y) (n : ℕ) :
    HasLiftingProperty (boundaryInclusion n) p ↔
      HasLiftingProperty (SSet.toTop.map (boundary n).ι) p :=
  HasLiftingProperty.iff_of_arrow_iso_left (boundaryArrowIso n) p

end

end Thomason.Construction.RealizedCube

end

section

/-! # Realization preserves products with standard simplices -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Iterated cylinder coordinates give an actual product homeomorphism
when the right simplicial factor is a finite cube. -/
def realizationCubeProductHomeomorph (X : SSet.{0}) (n : ℕ) :
    SSet.toTop.obj (X ⊗ RealizedCube.obj n) ≃ₜ
      (SSet.toTop.obj X × SSet.toTop.obj (RealizedCube.obj n)) :=
  match n with
  | 0 => (TopCat.homeoOfIso (SSet.toTop.mapIso
      (whiskerLeftIso X unitZeroIso.symm ≪≫ ρ_ X))).trans
      (Homeomorph.prodUnique (SSet.toTop.obj X) (SSet.toTop.obj (Δ[0] : SSet.{0}))).symm
  | n+1 =>
    (TopCat.homeoOfIso (SSet.toTop.mapIso (α_ X (RealizedCube.obj n) Δ[1]).symm)).trans
    ((RealizedCylinder.cylinderHomeomorph (X ⊗ RealizedCube.obj n)).symm.trans
    (((realizationCubeProductHomeomorph X n).prodCongr (Homeomorph.refl _)).trans
    ((Homeomorph.prodAssoc _ _ _).trans
      ((Homeomorph.refl _).prodCongr (RealizedCylinder.cylinderHomeomorph (RealizedCube.obj n))))))

/-- The homeomorphism's first coordinate is the actual realized projection. -/
theorem realizationCubeProductHomeomorph_fst (X : SSet.{0}) (n : ℕ)
    (z : SSet.toTop.obj (X ⊗ RealizedCube.obj n)) :
    (realizationCubeProductHomeomorph X n z).1 =
      (SSet.toTop.map (fst X (RealizedCube.obj n))).hom z := by
  induction n with
  | zero =>
    change (SSet.toTop.map (X ◁ unitZeroIso.inv ≫ (ρ_ X).hom)).hom z = _
    rw [rightUnitor_hom, whiskerLeft_fst]
    rfl
  | succ n ih =>
    change (realizationCubeProductHomeomorph X n
      ((SSet.toTop.map (fst (X ⊗ RealizedCube.obj n) Δ[1])).hom
        ((SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv).hom z))).1 = _
    rw [ih]
    change (SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv ≫
      SSet.toTop.map (fst (X ⊗ RealizedCube.obj n) Δ[1]) ≫
      SSet.toTop.map (fst X (RealizedCube.obj n))).hom z = _
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, associator_inv_fst_fst]
    rfl

/-- Its second coordinate is likewise the actual projection, so the
homeomorphism is exactly the canonical comparison. -/
theorem realizationCubeProductHomeomorph_snd (X : SSet.{0}) (n : ℕ)
    (z : SSet.toTop.obj (X ⊗ RealizedCube.obj n)) :
    (realizationCubeProductHomeomorph X n z).2 =
      (SSet.toTop.map (snd X (RealizedCube.obj n))).hom z := by
  induction n with
  | zero => exact @Subsingleton.elim (SSet.toTop.obj (Δ[0] : SSet.{0})) inferInstance _ _
  | succ n ih =>
    apply (RealizedCylinder.cylinderHomeomorph (RealizedCube.obj n)).symm.injective
    change (RealizedCylinder.cylinderHomeomorph (RealizedCube.obj n)).symm
      ((RealizedCylinder.cylinderHomeomorph (RealizedCube.obj n))
      ((realizationCubeProductHomeomorph X n
      ((SSet.toTop.map (fst (X ⊗ RealizedCube.obj n) Δ[1])).hom
        ((SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv).hom z))).2,
      PrismBarycentric.realizationTime.hom
        ((SSet.toTop.map (snd (X ⊗ RealizedCube.obj n) Δ[1])).hom
          ((SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv).hom z)))) = _
    refine ((RealizedCylinder.cylinderHomeomorph (RealizedCube.obj n)).symm_apply_apply _).trans ?_
    apply Prod.ext
    · rw [ih]
      change (SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv ≫
        SSet.toTop.map (fst (X ⊗ RealizedCube.obj n) Δ[1]) ≫
        SSet.toTop.map (snd X (RealizedCube.obj n))).hom z =
        (SSet.toTop.map (snd X (RealizedCube.obj (n+1))) ≫
          SSet.toTop.map (fst (RealizedCube.obj n) Δ[1])).hom z
      simp only [← SSet.toTop.map_comp, associator_inv_fst_snd]
      rw [SSet.toTop.map_comp]
      rfl
    · change PrismBarycentric.realizationTime.hom
        ((SSet.toTop.map (α_ X (RealizedCube.obj n) Δ[1]).inv ≫
          SSet.toTop.map (snd (X ⊗ RealizedCube.obj n) Δ[1])).hom z) =
        PrismBarycentric.realizationTime.hom
          ((SSet.toTop.map (snd X (RealizedCube.obj (n+1))) ≫
            SSet.toTop.map (snd (RealizedCube.obj n) Δ[1])).hom z)
      simp only [← SSet.toTop.map_comp, associator_inv_snd]
      rw [SSet.toTop.map_comp]
      rfl

/-- The canonical realization comparison for products with finite cubes
is an isomorphism of topological spaces. -/
theorem realizationProductComparison_cube_isIso (X : SSet.{0}) (n : ℕ) :
    IsIso (realizationProductComparison X (RealizedCube.obj n)) := by
  have he : realizationProductComparison X (RealizedCube.obj n) =
      (TopCat.isoOfHomeo (realizationCubeProductHomeomorph X n)).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Prod.ext (realizationCubeProductHomeomorph_fst X n z).symm
      (realizationCubeProductHomeomorph_snd X n z).symm
  rw [he]
  infer_instance

/-- The canonical cube product comparison as an explicit isomorphism. -/
def realizationCubeProductIso (X : SSet.{0}) (n : ℕ) :
    SSet.toTop.obj (X ⊗ RealizedCube.obj n) ≅
      TopCat.of (SSet.toTop.obj X × SSet.toTop.obj (RealizedCube.obj n)) := by
  have := realizationProductComparison_cube_isIso X n
  exact asIso (realizationProductComparison X (RealizedCube.obj n))

/-- The actual canonical comparison for an arbitrary simplicial set and
a standard simplex is a homeomorphism, by its explicit cube retraction. -/
theorem realizationProductComparison_simplex_isIso (X : SSet.{0}) (n : ℕ) :
    IsIso (realizationProductComparison X (Δ[n] : SSet.{0})) := by
  have := realizationProductComparison_cube_isIso X n
  exact realizationProductComparison_isIso_of_retract X (simplexToCube n)
    (cubeToSimplex n) (simplexToCube_cubeToSimplex n)

/-- Product realization with a simplex, with the actual two projections. -/
def realizationSimplexProductHomeomorph (X : SSet.{0}) (n : ℕ) :
    SSet.toTop.obj (X ⊗ (Δ[n] : SSet.{0})) ≃ₜ
      (SSet.toTop.obj X × SSet.toTop.obj (Δ[n] : SSet.{0})) := by
  have := realizationProductComparison_simplex_isIso X n
  exact TopCat.homeoOfIso (asIso (realizationProductComparison X (Δ[n] : SSet.{0})))

end

end Thomason.Construction

end

section

/-! # Realization commutes with products having a finite parameter -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- The canonical comparison is natural also in its first factor. -/
theorem realizationProductComparison_naturality_left {X X' : SSet.{0}}
    (f : X ⟶ X') (Y : SSet.{0}) :
    SSet.toTop.map (f ▷ Y) ≫ realizationProductComparison X' Y =
      realizationProductComparison X Y ≫ (SSet.toTop.map f ▷ SSet.toTop.obj Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · change (SSet.toTop.map (f ▷ Y) ≫ SSet.toTop.map (fst X' Y)).hom z =
      (SSet.toTop.map (fst X Y) ≫ SSet.toTop.map f).hom z
    rw [← SSet.toTop.map_comp, whiskerRight_fst, SSet.toTop.map_comp]
  · change (SSet.toTop.map (f ▷ Y) ≫ SSet.toTop.map (snd X' Y)).hom z =
      (SSet.toTop.map (snd X Y)).hom z
    rw [← SSet.toTop.map_comp, whiskerRight_snd]

/-- Regard the actual product comparison as a map of colimit diagrams. -/
def realizationProductRightComparison (Y : SSet.{0}) :
    tensorRight Y ⋙ SSet.toTop ⟶ SSet.toTop ⋙ tensorRight (SSet.toTop.obj Y) where
  app X := realizationProductComparison X Y
  naturality _ _ f := realizationProductComparison_naturality_left f Y

/-- Symmetry reduces a standard simplex in the left factor to the already
constructed right-simplex product homeomorphism. -/
theorem realizationProductComparison_simplex_left_isIso (n : ℕ) (Y : SSet.{0}) :
    IsIso (realizationProductComparison (Δ[n] : SSet.{0}) Y) := by
  have : IsIso (realizationProductComparison Y (Δ[n] : SSet.{0})) :=
    realizationProductComparison_simplex_isIso Y n
  have he : realizationProductComparison (Δ[n] : SSet.{0}) Y =
      SSet.toTop.map (β_ (Δ[n] : SSet.{0}) Y).hom ≫
        realizationProductComparison Y (Δ[n] : SSet.{0}) ≫
          (β_ (SSet.toTop.obj Y) (SSet.toTop.obj (Δ[n] : SSet.{0}))).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Prod.ext
    · change (SSet.toTop.map (fst (Δ[n] : SSet.{0}) Y)).hom z =
        (SSet.toTop.map (snd Y (Δ[n] : SSet.{0}))).hom
          ((SSet.toTop.map (β_ (Δ[n] : SSet.{0}) Y).hom).hom z)
      have h := congrArg (fun k => (SSet.toTop.map k).hom z)
        (braiding_hom_snd (Δ[n] : SSet.{0}) Y)
      simpa only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] using h.symm
    · change (SSet.toTop.map (snd (Δ[n] : SSet.{0}) Y)).hom z =
        (SSet.toTop.map (fst Y (Δ[n] : SSet.{0}))).hom
          ((SSet.toTop.map (β_ (Δ[n] : SSet.{0}) Y).hom).hom z)
      have h := congrArg (fun k => (SSet.toTop.map k).hom z)
        (braiding_hom_fst (Δ[n] : SSet.{0}) Y)
      simpa only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] using h.symm
  rw [he]
  change IsIso ((SSet.toTop.mapIso (β_ (Δ[n] : SSet.{0}) Y) ≪≫
    asIso (realizationProductComparison Y (Δ[n] : SSet.{0})) ≪≫
      β_ (SSet.toTop.obj Y) (SSet.toTop.obj (Δ[n] : SSet.{0}))).hom)
  infer_instance

/-- A locally compact realization in the fixed factor lets the comparison
pass from standard simplices to the actual simplex colimit. -/
theorem realizationProductComparison_isIso_of_locallyCompact (X Y : SSet.{0})
    [LocallyCompactSpace (SSet.toTop.obj Y)] :
    IsIso (realizationProductComparison X Y) := by
  let := TopologicalProduct.preservesColimits (SSet.toTop.obj Y)
  let D := CostructuredArrow.proj SSet.stdSimplex X ⋙ SSet.stdSimplex
  let a := realizationProductRightComparison Y
  have : ∀ j, IsIso ((Functor.whiskerLeft D a).app j) := fun j =>
    realizationProductComparison_simplex_left_isIso j.left.len Y
  have : IsIso (Functor.whiskerLeft D a) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit D a
    (Presheaf.tautologicalCocone' X) (Presheaf.isColimitTautologicalCocone' X)

/-- Every finite simplicial parameter has a compact Hausdorff realization,
so its product with any actual realization has the canonical topology. -/
theorem realizationProductComparison_finite_isIso (X Y : SSet.{0}) [Y.Finite] :
    IsIso (realizationProductComparison X Y) := by
  let := RealizationPrism.compactSpace_of_finite Y
  let := RealizationPrism.finite_realization_t2Space Y
  exact realizationProductComparison_isIso_of_locallyCompact X Y

/-- The homeomorphism for finite parameter spaces retains both actual
realized projections, by construction from the canonical comparison. -/
def realizationFiniteProductHomeomorph (X Y : SSet.{0}) [Y.Finite] :
    SSet.toTop.obj (X ⊗ Y) ≃ₜ (SSet.toTop.obj X × SSet.toTop.obj Y) := by
  have := realizationProductComparison_finite_isIso X Y
  exact TopCat.homeoOfIso (asIso (realizationProductComparison X Y))

end

end Thomason.Construction

end

section

/-! # Product realization on subcomplexes, including full boundaries -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- A product with a subcomplex is exactly the inverse image under the
second simplicial projection, including all degenerate simplices. -/
def productSubcomplexIso (X Y : SSet.{0}) (A : Y.Subcomplex) :
    X ⊗ A.toSSet ≅ (A.preimage (snd X Y)).toSSet where
  hom := {
    app _ := ↾fun z => ⟨(z.1,z.2.val), z.2.property⟩
    naturality _ _ _ := rfl }
  inv := {
    app _ := ↾fun z => (z.val.1, ⟨z.val.2,z.property⟩)
    naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[reassoc] theorem productSubcomplexIso_hom_ι (X Y : SSet.{0}) (A : Y.Subcomplex) :
    (productSubcomplexIso X Y A).hom ≫ (A.preimage (snd X Y)).ι = X ◁ A.ι := rfl

/-- The subspace selected by the second coordinate is the ordinary
product with the selected subspace. -/
def productSubspaceHomeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set Y) : {z : X × Y // z.2 ∈ A} ≃ₜ (X × A) where
  toFun z := (z.val.1, ⟨z.val.2,z.property⟩)
  invFun z := ⟨(z.1,z.2.val),z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Any established product comparison restricts to an actual product
homeomorphism on every subcomplex of its right factor. -/
def realizationProductSubcomplexHomeomorph (X Y : SSet.{0}) (A : Y.Subcomplex)
    [IsIso (realizationProductComparison X Y)] :
    SSet.toTop.obj (X ⊗ A.toSSet) ≃ₜ
      (SSet.toTop.obj X × SSet.toTop.obj A.toSSet) :=
  let e := TopCat.homeoOfIso (asIso (realizationProductComparison X Y))
  let U := Set.range (SSet.toTop.map A.ι).hom
  let r := (RealizationPrism.inclusion_isClosedEmbedding Y A).isEmbedding.toHomeomorph
  (TopCat.homeoOfIso (SSet.toTop.mapIso (productSubcomplexIso X Y A))).trans
    ((RealizationPrism.preimageHomeomorph (snd X Y) A).trans
      ((e.subtype (p := fun z => (SSet.toTop.map (snd X Y)).hom z ∈ U)
        (q := fun z => z.2 ∈ U) (fun _ => Iff.rfl)).trans
        ((productSubspaceHomeomorph _ _ U).trans ((Homeomorph.refl _).prodCongr r.symm))))

/-- Its first coordinate is the original realized projection. -/
theorem realizationProductSubcomplexHomeomorph_fst (X Y : SSet.{0}) (A : Y.Subcomplex)
    [IsIso (realizationProductComparison X Y)] (z : SSet.toTop.obj (X ⊗ A.toSSet)) :
    (realizationProductSubcomplexHomeomorph X Y A z).1 =
      (SSet.toTop.map (fst X A.toSSet)).hom z := by
  change (SSet.toTop.map (fst X Y)).hom
    ((SSet.toTop.map (A.preimage (snd X Y)).ι).hom
      ((SSet.toTop.map (productSubcomplexIso X Y A).hom).hom z)) = _
  change (SSet.toTop.map (productSubcomplexIso X Y A).hom ≫
    SSet.toTop.map (A.preimage (snd X Y)).ι ≫ SSet.toTop.map (fst X Y)).hom z = _
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
    productSubcomplexIso_hom_ι_assoc, whiskerLeft_fst]

/-- Its second coordinate retains the entire subcomplex point. -/
theorem realizationProductSubcomplexHomeomorph_snd (X Y : SSet.{0}) (A : Y.Subcomplex)
    [IsIso (realizationProductComparison X Y)] (z : SSet.toTop.obj (X ⊗ A.toSSet)) :
    (realizationProductSubcomplexHomeomorph X Y A z).2 =
      (SSet.toTop.map (snd X A.toSSet)).hom z := by
  apply (RealizationPrism.inclusion_isClosedEmbedding Y A).injective
  change (SSet.toTop.map A.ι).hom
    (((RealizationPrism.inclusion_isClosedEmbedding Y A).isEmbedding.toHomeomorph).symm _) = _
  rw [show ∀ y, (SSet.toTop.map A.ι).hom
      (((RealizationPrism.inclusion_isClosedEmbedding Y A).isEmbedding.toHomeomorph).symm y) = y.val
    from fun y => congrArg Subtype.val
      (((RealizationPrism.inclusion_isClosedEmbedding Y A).isEmbedding.toHomeomorph).apply_symm_apply y)]
  change (SSet.toTop.map (productSubcomplexIso X Y A).hom ≫
    SSet.toTop.map (A.preimage (snd X Y)).ι ≫ SSet.toTop.map (snd X Y)).hom z =
    (SSet.toTop.map (snd X A.toSSet) ≫ SSet.toTop.map A.ι).hom z
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
    productSubcomplexIso_hom_ι_assoc, whiskerLeft_snd, SSet.toTop.map_comp]

/-- The homeomorphism just constructed is the canonical product comparison. -/
theorem realizationProductComparison_subcomplex_isIso (X Y : SSet.{0}) (A : Y.Subcomplex)
    [IsIso (realizationProductComparison X Y)] :
    IsIso (realizationProductComparison X A.toSSet) := by
  have he : realizationProductComparison X A.toSSet =
      (TopCat.isoOfHomeo (realizationProductSubcomplexHomeomorph X Y A)).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Prod.ext (realizationProductSubcomplexHomeomorph_fst X Y A z).symm
      (realizationProductSubcomplexHomeomorph_snd X Y A z).symm
  rw [he]
  infer_instance

/-- In particular the complete simplex boundary satisfies product realization. -/
theorem realizationProductComparison_boundary_isIso (X : SSet.{0}) (n : ℕ) :
    IsIso (realizationProductComparison X (SSet.boundary n).toSSet) := by
  have := realizationProductComparison_simplex_isIso X n
  exact realizationProductComparison_subcomplex_isIso X (Δ[n] : SSet.{0}) (SSet.boundary n)

/-- The complete finite cube boundary satisfies the same exact comparison. -/
theorem realizationProductComparison_cubeBoundary_isIso (X : SSet.{0}) (n : ℕ) :
    IsIso (realizationProductComparison X (RealizedCube.boundary n).toSSet) := by
  have := realizationProductComparison_cube_isIso X (n+1)
  exact realizationProductComparison_subcomplex_isIso X (RealizedCube.obj (n+1))
    (RealizedCube.boundary n)

end

end Thomason.Construction

end

section

/-! # Deformations with an initial stationary interval

The initial interval makes successive deformations compatible without
changing the time parameter on the earlier stages of a countable composite.
-/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory

noncomputable section

/-- A deformation toward a retract which waits until time `a`. -/
structure ScheduledData {A B : TopCat.{0}} (i : A ⟶ B) (a : ℝ) where
  retraction : B ⟶ A
  left_inv : i ≫ retraction = 𝟙 A
  homotopy : (ContinuousMap.id B).HomotopyRel (retraction ≫ i).hom (Set.range i.hom)
  idle : ∀ (t : unitInterval) (x : B), (t : ℝ) ≤ a → homotopy (t, x) = x

variable {A B C : TopCat.{0}} {i : A ⟶ B} {j : B ⟶ C} {a : ℝ}

/-- Forgetting the schedule gives ordinary stationary deformation data. -/
def ScheduledData.toData (d : ScheduledData i a) : Data i where
  retraction := d.retraction
  left_inv := d.left_inv
  homotopy := d.homotopy.symm

/-- The identity can wait for the entire interval. -/
def scheduledIdentity (A : TopCat.{0}) : ScheduledData (𝟙 A) 1 where
  retraction := 𝟙 A
  left_inv := Category.id_comp _
  homotopy := ContinuousMap.HomotopyRel.refl _ _
  idle := by intros; rfl

/-- The attaching deformation is completed during `[a/2,a]`. -/
def ScheduledData.early (_d : ScheduledData i a) (e : Data j) : C(unitInterval × C, C) where
  toFun p := e.homotopy.toHomotopy.symm.extend (((p.1 : ℝ) - a/2) / (a/2)) p.2
  continuous_toFun := e.homotopy.toHomotopy.symm.continuous.comp (by fun_prop)

/-- The later part is the old deformation, with its original time parameter. -/
def ScheduledData.late (d : ScheduledData i a) (e : Data j) : C(unitInterval × C, C) where
  toFun p := j.hom (d.homotopy (p.1, e.retraction.hom p.2))
  continuous_toFun := j.hom.continuous.comp (d.homotopy.continuous.comp (by fun_prop))

theorem ScheduledData.early_at_cut (d : ScheduledData i a) (e : Data j) (ha : 0 < a)
    (t : unitInterval) (x : C) (ht : (t : ℝ) = a) :
    d.early e (t, x) = j.hom (e.retraction.hom x) := by
  change e.homotopy.toHomotopy.symm.extend (((t : ℝ) - a/2) / (a/2)) x = _
  have hq : ((t : ℝ) - a/2) / (a/2) = 1 := by rw [ht]; field_simp; ring
  rw [hq, ContinuousMap.Homotopy.extend_one]
  rfl

theorem ScheduledData.early_idle (d : ScheduledData i a) (e : Data j) (ha : 0 < a)
    (t : unitInterval) (x : C) (ht : (t : ℝ) ≤ a/2) : d.early e (t, x) = x := by
  apply e.homotopy.toHomotopy.symm.extend_apply_of_le_zero
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by linarith)

/-- Join the new deformation to the old one at their common stationary value. -/
def ScheduledData.stepTrack (d : ScheduledData i a) (e : Data j) (ha : 0 < a) :
    C(unitInterval × C, C) where
  toFun p := if (p.1 : ℝ) ≤ a then d.early e p else d.late e p
  continuous_toFun := continuous_if_le (by fun_prop) continuous_const
    (d.early e).continuous.continuousOn (d.late e).continuous.continuousOn (by
      intro p hp
      rcases p with ⟨t, x⟩
      change (t : ℝ) = a at hp
      rw [d.early_at_cut e ha t x hp]
      change _ = j.hom (d.homotopy (t, e.retraction.hom x))
      rw [d.idle t _ hp.le])

theorem ScheduledData.stepTrack_low (d : ScheduledData i a) (e : Data j) (ha : 0 < a)
    (t : unitInterval) (x : C) (ht : (t : ℝ) ≤ a) :
    d.stepTrack e ha (t, x) = d.early e (t, x) := ite_eq_left ht

theorem ScheduledData.stepTrack_high (d : ScheduledData i a) (e : Data j) (ha : 0 < a)
    (t : unitInterval) (x : C) (ht : a ≤ (t : ℝ)) :
    d.stepTrack e ha (t, x) = d.late e (t, x) := by
  by_cases h : (t : ℝ) ≤ a
  · rw [d.stepTrack_low e ha t x h, d.early_at_cut e ha t x (le_antisymm h ht)]
    change _ = j.hom (d.homotopy (t, e.retraction.hom x))
    rw [d.idle t _ h]
  · exact ite_eq_right h

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Compatibility of successive scheduled deformations -/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory

noncomputable section

variable {A B C : TopCat.{0}} {i : A ⟶ B} {j : B ⟶ C} {a : ℝ}

/-- Even outside the original time interval, the extended track fixes the retract. -/
theorem ScheduledData.early_stationary (d : ScheduledData i a) (e : Data j)
    (t : unitInterval) (x : B) : d.early e (t, j.hom x) = j.hom x := by
  exact e.homotopy.symm.extendProp (((t : ℝ) - a/2) / (a/2))
    (j.hom x) (Set.mem_range_self x)

/-- The new track restricts to the previous track with exactly the same time. -/
theorem ScheduledData.stepTrack_compatible (d : ScheduledData i a) (e : Data j)
    (ha : 0 < a) (t : unitInterval) (x : B) :
    d.stepTrack e ha (t, j.hom x) = j.hom (d.homotopy (t, x)) := by
  by_cases ht : (t : ℝ) ≤ a
  · rw [d.stepTrack_low e ha _ _ ht, d.early_stationary e, d.idle _ _ ht]
  · rw [d.stepTrack_high e ha _ _ (le_of_not_ge ht)]
    change j.hom (d.homotopy (t, e.retraction.hom (j.hom x))) = _
    rw [show e.retraction.hom (j.hom x) = x from
      congrArg (fun f => f.hom x) e.left_inv]

/-- Extend a scheduled deformation across one additional stationary retract. -/
def ScheduledData.step (d : ScheduledData i a) (e : Data j)
    (ha : 0 < a) (ha' : a ≤ 1) : ScheduledData (i ≫ j) (a/2) where
  retraction := e.retraction ≫ d.retraction
  left_inv := by rw [Category.assoc, ← Category.assoc j e.retraction, e.left_inv]; simpa using d.left_inv
  homotopy := {
    toContinuousMap := d.stepTrack e ha
    map_zero_left := by
      intro x
      change d.stepTrack e ha (0, x) = x
      rw [d.stepTrack_low e ha 0 x (by simpa using ha.le)]
      exact d.early_idle e ha 0 x (by change (0 : ℝ) ≤ a/2; linarith)
    map_one_left := by
      intro x
      change d.stepTrack e ha (1, x) = _
      rw [d.stepTrack_high e ha 1 x (by simpa using ha')]
      change j.hom (d.homotopy (1, e.retraction.hom x)) = _
      exact congrArg j.hom (d.homotopy.map_one_left (e.retraction.hom x))
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      change d.stepTrack e ha (t, j.hom (i.hom x)) = j.hom (i.hom x)
      rw [d.stepTrack_compatible e ha]
      exact congrArg j.hom (d.homotopy.eq_fst t (Set.mem_range_self x)) }
  idle := by
    intro t x ht
    change d.stepTrack e ha (t, x) = x
    rw [d.stepTrack_low e ha t x (by linarith)]
    exact d.early_idle e ha t x ht

/-- Retractions also agree on the earlier stage. -/
theorem ScheduledData.step_retraction (d : ScheduledData i a) (e : Data j)
    (ha : 0 < a) (ha' : a ≤ 1) :
    j ≫ (d.step e ha ha').retraction = d.retraction := by
  change j ≫ (e.retraction ≫ d.retraction) = _
  rw [← Category.assoc, e.left_inv, Category.id_comp]

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Compatible finite stages of a countable deformation -/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Sequential

/-- The time reserved for subsequent attaching deformations. -/
def delay : ℕ → ℝ
  | 0 => 1
  | n+1 => delay n / 2

theorem delay_pos (n : ℕ) : 0 < delay n := by
  induction n with
  | zero => norm_num [delay]
  | succ n ih => exact div_pos ih (by norm_num)

theorem delay_le_one (n : ℕ) : delay n ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => dsimp [delay]; linarith [delay_pos n]

variable (X : ℕ ⥤ TopCat.{0})

/-- The actual successor map of the diagram. -/
abbrev next (n : ℕ) := X.map (homOfLE (Nat.le_succ n))

/-- The inclusion of stage zero, written recursively for the deformation construction. -/
def initial : (n : ℕ) → (X.obj 0 ⟶ X.obj n)
  | 0 => 𝟙 _
  | n+1 => initial n ≫ next X n

variable (d : ∀ n, Data (next X n))

/-- A compatible deformation at every finite stage. -/
def stage : (n : ℕ) → ScheduledData (initial X n) (delay n)
  | 0 => scheduledIdentity (X.obj 0)
  | n+1 => (stage n).step (d n) (delay_pos n) (delay_le_one n)

@[reassoc]
theorem stage_retraction (n : ℕ) :
    next X n ≫ (stage X d (n+1)).retraction = (stage X d n).retraction :=
  (stage X d n).step_retraction (d n) (delay_pos n) (delay_le_one n)

theorem stage_compatible (n : ℕ) (t : unitInterval) (x : X.obj n) :
    (stage X d (n+1)).homotopy (t, (next X n).hom x) =
      (next X n).hom ((stage X d n).homotopy (t, x)) :=
  (stage X d n).stepTrack_compatible (d n) (delay_pos n) t x

/-- Retractions form a cocone to the initial stage. -/
def retractCocone : Cocone X where
  pt := X.obj 0
  ι := NatTrans.ofSequence (fun n => (stage X d n).retraction) (by
    intro n
    change next X n ≫ (stage X d (n+1)).retraction = (stage X d n).retraction ≫ 𝟙 _
    rw [Category.comp_id]
    exact stage_retraction X d n)

variable {X} (c : Cocone X)

@[reassoc]
theorem initial_leg (n : ℕ) : initial X n ≫ c.ι.app n = c.ι.app 0 := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    change (initial X n ≫ next X n) ≫ c.ι.app (n+1) = _
    rw [Category.assoc, c.w (homOfLE (Nat.le_succ n))]
    exact ih

variable (d : ∀ n, Data (next X n))

/-- Finite tracks mapped into the actual colimit cocone. -/
def trackLeg (n : ℕ) : TopologicalInterval.cylinder.obj (X.obj n) ⟶ c.pt :=
  TopCat.ofHom ⟨fun p => (c.ι.app n).hom ((stage X d n).homotopy (p.2, p.1)),
    (c.ι.app n).hom.continuous.comp ((stage X d n).homotopy.continuous.comp (by fun_prop))⟩

@[reassoc]
theorem trackLeg_next (n : ℕ) :
    TopologicalInterval.cylinder.map (next X n) ≫ trackLeg c d (n+1) = trackLeg c d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change (c.ι.app (n+1)).hom ((stage X d (n+1)).homotopy (p.2, (next X n).hom p.1)) = _
  rw [stage_compatible]
  exact congrArg (fun f => f.hom ((stage X d n).homotopy (p.2, p.1)))
    (c.w (homOfLE (Nat.le_succ n)))

/-- Tracks form a cocone after product with the interval. -/
def trackCocone : Cocone (X ⋙ TopologicalInterval.cylinder) where
  pt := c.pt
  ι := NatTrans.ofSequence (trackLeg c d) (by
    intro n
    change TopologicalInterval.cylinder.map (next X n) ≫ trackLeg c d (n+1) =
      trackLeg c d n ≫ 𝟙 _
    rw [Category.comp_id]
    exact trackLeg_next c d n)

end Sequential

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Countable compositions of stationary deformations

The compatible scheduled tracks descend through the actual colimit after
product with the interval. No compactness or weak-equivalence closure
assumption is used.
-/

namespace Thomason.Construction.TopologicalDeformation.Sequential

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {X : ℕ ⥤ TopCat.{0}} {c : Cocone X} (hc : IsColimit c)
  (d : ∀ n, Data (next X n))

/-- The compatible stage retractions descend to the colimit. -/
def retraction : c.pt ⟶ X.obj 0 := hc.desc (retractCocone X d)

@[reassoc]
theorem retraction_fac (n : ℕ) :
    c.ι.app n ≫ retraction hc d = (stage X d n).retraction :=
  hc.fac (retractCocone X d) n

/-- Product with the interval preserves the colimit used to assemble the tracks. -/
def track : TopologicalInterval.cylinder.obj c.pt ⟶ c.pt :=
  (isColimitOfPreserves TopologicalInterval.cylinder hc).desc (trackCocone c d)

@[reassoc]
theorem track_fac (n : ℕ) :
    TopologicalInterval.cylinder.map (c.ι.app n) ≫ track hc d = trackLeg c d n :=
  (isColimitOfPreserves TopologicalInterval.cylinder hc).fac (trackCocone c d) n

theorem retraction_left : c.ι.app 0 ≫ retraction hc d = 𝟙 (X.obj 0) :=
  retraction_fac hc d 0

/-- The assembled track starts at the identity. -/
theorem track_zero : TopologicalInterval.sectionAt c.pt 0 ≫ track hc d = 𝟙 c.pt := by
  apply hc.hom_ext
  intro n
  rw [← Category.assoc, section_naturality, Category.assoc, track_fac]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (c.ι.app n).hom ((stage X d n).homotopy (0, x)) = (c.ι.app n).hom x
  exact congrArg (c.ι.app n).hom ((stage X d n).homotopy.map_zero_left x)

/-- At the end, every stage has been retracted to stage zero. -/
theorem track_one :
    TopologicalInterval.sectionAt c.pt 1 ≫ track hc d = retraction hc d ≫ c.ι.app 0 := by
  apply hc.hom_ext
  intro n
  rw [← Category.assoc, section_naturality, Category.assoc, track_fac]
  rw [← Category.assoc (c.ι.app n), retraction_fac]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (c.ι.app n).hom ((stage X d n).homotopy (1, x)) =
    (c.ι.app 0).hom ((stage X d n).retraction.hom x)
  calc
    _ = (c.ι.app n).hom ((initial X n).hom ((stage X d n).retraction.hom x)) :=
      congrArg (c.ι.app n).hom ((stage X d n).homotopy.map_one_left x)
    _ = _ := congrArg (fun f => f.hom ((stage X d n).retraction.hom x)) (initial_leg c n)

/-- The initial stage is fixed throughout the assembled deformation. -/
theorem track_stationary (t : unitInterval) (x : X.obj 0) :
    (track hc d).hom ((c.ι.app 0).hom x, t) = (c.ι.app 0).hom x := by
  have h := congrArg (fun f => f.hom (x, t)) (track_fac hc d 0)
  exact h

/-- A countable composite of stationary deformation inclusions is again one. -/
def colimitData : Data (c.ι.app 0) where
  retraction := retraction hc d
  left_inv := retraction_left hc d
  homotopy := (show (ContinuousMap.id c.pt).HomotopyRel
      (retraction hc d ≫ c.ι.app 0).hom (Set.range (c.ι.app 0).hom) from {
    toFun := fun p => (track hc d).hom (p.2, p.1)
    continuous_toFun := (track hc d).hom.continuous.comp (by fun_prop)
    map_zero_left := fun x => congrArg (fun f => f.hom x) (track_zero hc d)
    map_one_left := fun x => congrArg (fun f => f.hom x) (track_one hc d)
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      exact track_stationary hc d t x }).symm

include hc d in
/-- The actual homotopy-group test for the countable colimit inclusion. -/
theorem colimit_weak : topologicalWeakEquivalences (c.ι.app 0) := by
  let e := colimitData hc d
  apply weakEquivalence_of_strongDeformationRetract (c.ι.app 0).hom e.retraction.hom _ e.homotopy
  exact congrArg TopCat.Hom.hom e.left_inv

end

end Thomason.Construction.TopologicalDeformation.Sequential

end

section

/-! # The actual singular simplicial set is Kan

A singular horn extends by precomposition with the explicitly constructed
retraction of its geometric realization. This uses the actual
realization/singular adjunction and no model-category input.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- An explicit filler of any horn in the singular simplicial set. -/
def singularHornFiller (X : TopCat.{0}) {n : ℕ} (i : Fin (n+2))
    (f : (Λ[n+1, i] : SSet.{0}) ⟶ TopCat.toSSet.obj X) :
    (Δ[n+1] : SSet.{0}) ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ X
    ((realizedHornData i).retraction ≫ (sSetTopAdj.homEquiv _ X).symm f)

@[reassoc]
theorem singularHornFiller_fac (X : TopCat.{0}) {n : ℕ} (i : Fin (n+2))
    (f : (Λ[n+1, i] : SSet.{0}) ⟶ TopCat.toSSet.obj X) :
    Λ[n+1, i].ι ≫ singularHornFiller X i f = f := by
  rw [singularHornFiller, ← sSetTopAdj.homEquiv_naturality_left,
    ← Category.assoc, (realizedHornData i).left_inv, Category.id_comp,
    Equiv.apply_symm_apply]

/-- Singular simplicial sets satisfy the genuine horn-filling condition. -/
theorem singular_kan (X : TopCat.{0}) : SSet.KanComplex (TopCat.toSSet.obj X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  refine ⟨singularHornFiller X i hf.desc, ?_⟩
  intro j hj
  rw [← SSet.horn.ι_ι i j hj, Category.assoc, singularHornFiller_fac]
  exact hf.ι_desc j hj

end

end Thomason.Construction

end

end OAI
