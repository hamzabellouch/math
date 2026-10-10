import Mathlib
import OAI.GroupTheory.FiniteType.InducedFree
import OAI.GroupTheory.FiniteType.ProductCriterion

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductFiniteResolution
variable {k G : Type} [CommRing k] [Group G]
def Beginning.ofComplex (C : ChainComplex (Rep k G) ℕ)
    (ε : C.X 0 ⟶ Rep.trivial k G k) [Epi ε]
    (w : C.d 1 0 ≫ ε = 0) (he0 : (ShortComplex.mk (C.d 1 0) ε w).Exact)
    (he1 : C.ExactAt 1) (α : ℕ → Type) [∀ n, Finite (α n)]
    (e : ∀ n, C.X n ≅ Rep.free k G (α n)) : Beginning (Rep.trivial k G k) where
  α₀ := α 0
  α₁ := α 1
  α₂ := α 2
  d₁ := (e 1).inv ≫ C.d 1 0 ≫ (e 0).hom
  d₂ := (e 2).inv ≫ C.d 2 1 ≫ (e 1).hom
  ε := (e 0).inv ≫ ε
  d₂_d₁ := by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Category.assoc (C.d 2 1),
    C.d_comp_d,zero_comp,comp_zero]
  d₁_ε := by simp only [Category.assoc,Iso.hom_inv_id_assoc,w,comp_zero]
  exact₁ := by
    have he := (HomologicalComplex.exactAt_iff' C 2 1 0 (by simp) (by simp)).mp he1
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (e 2) (e 1) (e 0)
      ((e 2).hom_inv_id_assoc (C.d 2 1 ≫ (e 1).hom))
      ((e 1).hom_inv_id_assoc (C.d 1 0 ≫ (e 0).hom)))).mp he
  exact₀ := by
    let E := ShortComplex.mk (C.d 1 0) ε w
    let F := ShortComplex.mk ((e 1).inv ≫ C.d 1 0 ≫ (e 0).hom) ((e 0).inv ≫ ε)
      (by simp only [Category.assoc,Iso.hom_inv_id_assoc,w,comp_zero])
    let iso : E ≅ F := ShortComplex.isoMk (e 1) (e 0) (Iso.refl _)
      (by dsimp [E,F]; simp only [Iso.hom_inv_id_assoc])
      (by dsimp [E,F]; simp only [Iso.hom_inv_id_assoc,Category.comp_id])
    exact (ShortComplex.exact_iff_of_iso iso).mp he0

end ProductFiniteResolution

namespace PresentationGeometry.FiniteStage
open Set Topology CWExtension CWEquivariant
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def algebraicBeginning (S : Stage G 0) : ProductFiniteResolution.Beginning (Rep.trivial ℤ G ℤ) := by
  let W := S.core
  letI := CoreDeck.leftAction W
  letI := CoreDeck.continuousLeftAction W (CoreDeck.of_potential W S.pot S.coord)
  let cov := DiscreteCoverCharts.covering W
  letI : T2Space W.TotalSpace := CoveringCellGeometry.hausdorff cov
  letI : Fact (∀ (g : G) (x : W.TotalSpace), W.proj (g • x) = W.proj x) := ⟨fun _ _ => rfl⟩
  letI : PathConnectedSpace (univ : Set W.TotalSpace) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_univ
  letI := CoveringCW.cwComplex_general cov
  letI : ∀ n, MulAction G (RelCWComplex.cell (univ : Set W.TotalSpace) n) :=
    fun n => EquivariantCoverCells.cellAction (p := W.proj) n
  have hc : ∀ (g : G) n (c : RelCWComplex.cell (univ : Set W.TotalSpace) n) (v : Disk n),
      g • RelCWComplex.map n c v = RelCWComplex.map n (g • c) v :=
    EquivariantCoverCells.chart_smul cov
  have e (n : ℕ) : object (G := G) (X := W.TotalSpace) n ≅
      Rep.free ℤ G (RelCWComplex.cell (univ : Set S.X) n) :=
    EquivariantCoverCells.freeIso (CoreDeck.left_free W) (CoreDeck.left_transitive W)
      (fun x => ⟨⟨x,(1:G)⟩,rfl⟩) n
  have he : (complex hc).ExactAt 1 := complex_exactAt hc 0 (by
    apply SingularAction.univ_homology_zero
    exact HurewiczConstruction.homology_zero_of_homotopy S.connectivity ⟨S.point,(1:G)⟩)
  letI : ∀ n, Finite (RelCWComplex.cell (univ : Set S.X) n) :=
    fun n => RelCWComplex.FiniteType.finite_cell n
  exact @ProductFiniteResolution.Beginning.ofComplex ℤ G _ _ (complex hc) (aug hc)
    (aug_epi hc) (d_aug hc) (aug_exact hc) he
    (fun n => RelCWComplex.cell (univ : Set S.X) n) inferInstance e
end PresentationGeometry.FiniteStage

namespace ProductFiniteResolution
variable (G : Type) [Group G] [Group.IsFinitelyPresented G]
theorem beginning_exists : Nonempty (Beginning (Rep.trivial ℤ G ℤ)) := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  obtain ⟨S⟩ := PresentationGeometry.FiniteStage.initialStage_exists G
  exact ⟨PresentationGeometry.FiniteStage.algebraicBeginning S⟩

theorem finite_free_resolution_of_products
    (hz : ∀ (I : Type) (n : ℕ), 2 ≤ n → IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    ∃ P : ProjectiveResolution (Rep.trivial ℤ G ℤ),
      ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free ℤ G α) := by
  obtain ⟨B⟩ := beginning_exists G
  exact exists_finite_free_resolution B hz
end ProductFiniteResolution

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
variable {G V I : Type} [Group G] [MulAction G V]
abbrev perm (G V : Type) [Group G] [MulAction G V] :=
  FunctionalTree.diagonalRep (V := V) (Rep.trivial ℤ G ℤ)

@[simp] lemma perm_single (g : G) (v : V) (r : ℤ) :
    (perm G V).ρ g (Finsupp.single v r) = Finsupp.single (g • v) r := by
  rw [FunctionalTree.diagonalRep_single]
  rfl

variable (A : Rep ℤ G) in
def tensorPermIso : A ⊗ perm G V ≅ FunctionalTree.diagonalRep (V := V) A := by
  classical
  exact Rep.mkIso (Representation.Equiv.mk (((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V))) (fun g => by
    apply TensorProduct.ext
    apply DFunLike.ext
    intro a
    apply Finsupp.lhom_ext
    intro v r
    change ((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V))
      (A.ρ g a ⊗ₜ[ℤ] ((perm G V).ρ g (Finsupp.single v r))) =
      (FunctionalTree.diagonalRep (V := V) A).ρ g
        (((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V)) (a ⊗ₜ[ℤ] Finsupp.single v r))
    rw [perm_single]
    simp only [LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.finsuppScalarLeft_apply_tmul]
    rw [Finsupp.sum_single_index (by
      exact (congrArg (Finsupp.single (g • v)) (Module.zero_smul (R := ℤ) ((A.ρ g) a))).trans (Finsupp.single_zero _)), Finsupp.sum_single_index (by
      exact (congrArg (Finsupp.single v) (Module.zero_smul (R := ℤ) a)).trans (Finsupp.single_zero _))]
    rw [FunctionalTree.diagonalRep_single]
    exact congrArg (Finsupp.single (g • v)) ((A.ρ g).map_smul r a).symm))

lemma coordinates_iso {C D : Rep ℤ G} (e : C ≅ D)
    (hb : Function.Bijective (ProductCriterion.coordinates (I := I) C)) :
    Function.Bijective (ProductCriterion.coordinates (I := I) D) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj (RegularProductR.rep ℤ G I)
  let E := F.mapIso e
  have hn (x : F.obj C) (i : I) :
      ProductCriterion.coordinate D i (E.hom x) =
      e.hom.hom (ProductCriterion.coordinate C i x) :=
    ProductCriterion.coordinate_natural D e.hom i x
  refine ⟨?_,?_⟩
  · intro x y he
    obtain ⟨a,rfl⟩ := (ModuleCat.epi_iff_surjective E.hom).mp inferInstance x
    obtain ⟨b,rfl⟩ := (ModuleCat.epi_iff_surjective E.hom).mp inferInstance y
    congr 1
    apply hb.injective
    funext i
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    change e.hom.hom (ProductCriterion.coordinate C i a) = e.hom.hom (ProductCriterion.coordinate C i b)
    rw [← hn,← hn]
    exact congrFun he i
  · intro z
    obtain ⟨a,ha⟩ := hb.surjective (fun i => e.inv.hom (z i))
    refine ⟨E.hom a,?_⟩
    funext i
    change ProductCriterion.coordinate D i (E.hom a) = z i
    rw [hn]
    change e.hom.hom (ProductCriterion.coordinates C a i) = z i
    rw [congrFun ha i]
    exact congrArg (fun f : D ⟶ D => f.hom (z i)) e.inv_hom_id

lemma coordinates_split {J : Type} [Fintype J] {C : Rep ℤ G} (D : J → Rep ℤ G)
    (inc : ∀ j, D j ⟶ C) (proj : ∀ j, C ⟶ D j)
    (h : ∑ j, proj j ≫ inc j = 𝟙 C)
    (hb : ∀ j, Function.Bijective (ProductCriterion.coordinates (I := I) (D j))) :
    Function.Bijective (ProductCriterion.coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj (RegularProductR.rep ℤ G I)
  have hf : ∑ j, F.map (proj j) ≫ F.map (inc j) = 𝟙 (F.obj C) := by
    simpa only [Functor.map_sum,Functor.map_comp,CategoryTheory.Functor.map_id] using congrArg F.map h
  refine ⟨?_,?_⟩
  · intro x y he
    have hj (j : J) : F.map (proj j) x = F.map (proj j) y := by
      apply (hb j).injective
      funext i
      change ProductCriterion.coordinate (D j) i (ProductCriterion.tensorMap _ (proj j) x) =
        ProductCriterion.coordinate (D j) i (ProductCriterion.tensorMap _ (proj j) y)
      rw [ProductCriterion.coordinate_natural,ProductCriterion.coordinate_natural]
      exact congrArg (proj j).hom (congrFun he i)
    have hh (z : F.obj C) : z = ∑ j, F.map (inc j) (F.map (proj j) z) := by
      have hhz := congrArg (fun f : F.obj C ⟶ F.obj C => f z) hf
      simpa using hhz.symm
    rw [hh x,hh y]
    congr 1
    funext j
    rw [hj]
  · intro z
    choose x hx using fun j => (hb j).surjective (fun i => (proj j).hom (z i))
    refine ⟨∑ j, F.map (inc j) (x j),?_⟩
    funext i
    change ProductCriterion.coordinate C i (∑ j, F.map (inc j) (x j)) = z i
    rw [map_sum]
    have hterm (j : J) : ProductCriterion.coordinate C i (F.map (inc j) (x j)) =
        (inc j).hom ((proj j).hom (z i)) := by
      change ProductCriterion.coordinate C i (ProductCriterion.tensorMap _ (inc j) (x j)) = _
      rw [ProductCriterion.coordinate_natural]
      exact congrArg (inc j).hom (congrFun (hx j) i)
    simp_rw [hterm]
    have he := congrArg (fun f : C ⟶ C => f.hom.toLinearMap (z i)) h
    simp only [Rep.sum_hom,Representation.IntertwiningMap.toLinearMap_sum,
      LinearMap.sum_apply] at he
    exact he

variable (G V) in
lemma coordinates_perm [Finite (OrbitCoefficients.Orbits (G := G) V)]
    (hp : ∀ v : V, Nonempty (OrbitModule.Presentation (Rep.trivial ℤ (MulAction.stabilizer G v) ℤ))) :
    Function.Bijective (ProductCriterion.coordinates (I := I) (perm G V)) := by
  classical
  let A := Rep.trivial ℤ G ℤ
  let := Fintype.ofFinite (OrbitCoefficients.Orbits (G := G) V)
  apply coordinates_split (fun j : OrbitCoefficients.Orbits (G := G) V =>
    FunctionalTree.diagonalRep (V := j.orbit) A)
    (OrbitCoefficients.orbitInclusion A) (OrbitCoefficients.orbitProjection A)
    (OrbitCoefficients.sum_projections A)
  intro j
  obtain ⟨P⟩ := hp j.out
  let Q := P.induced (MulAction.stabilizer G j.out).subtype
  let e := CosetInduction.indCosetIso (MulAction.stabilizer G j.out) A ≪≫
    OrbitCoefficients.orbitCosetIso A j
  apply coordinates_iso e
  exact @ProductCriterion.coordinates_of_presentation ℤ G I _ _ _ Q.α Q.β
    Q.finiteα Q.finiteβ Q.d Q.ε Q.epi Q.w Q.exact

variable (G V) in
lemma acyclic_perm [Finite (OrbitCoefficients.Orbits (G := G) V)]
    (hz : ∀ v : V, ∀ (J : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G v) J) (n+1))) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I ⊗ perm G V) (n+1)) := by
  apply IsZero.of_iso _ ((groupHomology.functor ℤ G (n+1)).mapIso
    (tensorPermIso (V := V) (RegularProductR.rep ℤ G I)))
  apply OrbitCoefficients.homology_zero
  intro j
  let S := MulAction.stabilizer G j.out
  have ha := ListChains.productCoefficient_vanishing S I (G ⧸ S) n (fun J => hz j.out J n)
  exact ha.of_iso ((groupHomology.functor ℤ S (n+1)).mapIso (RegularProduct.restrictionIso G I S))
end OrbitBrown

end

end OAI
