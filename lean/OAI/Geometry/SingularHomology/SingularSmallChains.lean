import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyConstant
import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

abbrev singularSet (X : Type) [TopologicalSpace X] : SSet :=
  TopCat.toSSet.obj (TopCat.of X)

def inSubset (s : Set X) : (singularSet X).Subcomplex where
  obj n := {σ | ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) n σ p ∈ s}
  map {n m} f σ hσ := by
    intro p
    exact hσ (Convexity.StdSimplex.map f.unop p)

@[simp] theorem mem_inSubset {s : Set X} {n : SimplexCategoryᵒᵖ}
    (σ : (singularSet X).obj n) :
    σ ∈ (inSubset s).obj n ↔
      Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ s := by
  simp only [inSubset, Set.mem_ofPred_eq, Set.range_subset_iff]

theorem inSubset_mono {s t : Set X} (h : s ⊆ t) : inSubset s ≤ inSubset t := by
  intro n σ hσ p
  exact h (hσ p)

@[simp] theorem inSubset_univ : inSubset (Set.univ : Set X) = ⊤ := by
  ext n σ
  simp [inSubset]

@[simp] theorem inSubset_inter (s t : Set X) :
    inSubset (s ∩ t) = inSubset s ⊓ inSubset t := by
  ext n σ
  simp [inSubset, forall_and]

def small {ι : Type*} (U : ι → Set X) : (singularSet X).Subcomplex :=
  ⨆ i, inSubset (U i)

@[simp] theorem mem_small {ι : Type*} (U : ι → Set X)
    {n : SimplexCategoryᵒᵖ} (σ : (singularSet X).obj n) :
    σ ∈ (small U).obj n ↔
      ∃ i, Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ U i := by
  simp [small]

theorem small_mono_of_refinement {ι κ : Type*} {U : ι → Set X} {V : κ → Set X}
    (h : ∀ i, ∃ j, U i ⊆ V j) : small U ≤ small V := by
  apply iSup_le
  intro i
  obtain ⟨j, hij⟩ := h i
  exact (inSubset_mono hij).trans (le_iSup (fun j => inSubset (V j)) j)

theorem small_le_inSubset_iUnion {ι : Type*} (U : ι → Set X) :
    small U ≤ inSubset (⋃ i, U i) := by
  apply iSup_le
  intro i
  exact inSubset_mono (Set.subset_iUnion U i)

abbrev chains {ι : Type*} (U : ι → Set X) :=
  (small U : SSet).chainComplex (ModuleCat.of ℝ ℝ)

def inclusion {ι : Type*} (U : ι → Set X) : chains U ⟶ realSingularChainComplex X :=
  SSet.chainComplexMap (small U).ι (ModuleCat.of ℝ ℝ)

instance inclusion_f_mono {ι : Type*} (U : ι → Set X) (n : ℕ) :
    Mono ((inclusion U).f n) := by
  change Mono ((sigmaConst.obj (ModuleCat.of ℝ ℝ)).map ((small U).ι.app (op ⦋n⦌)))
  infer_instance

theorem inclusion_f_injective {ι : Type*} (U : ι → Set X) (n : ℕ) :
    Function.Injective ((inclusion U).f n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

def subspaceMap (s : Set X) : singularSet s ⟶ inSubset s where
  app n := TypeCat.ofHom fun σ =>
    ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).app n σ,
      fun p => (TopCat.toSSetObjEquiv (TopCat.of s) n σ p).property⟩
  naturality {n m} f := by
    ext σ
    apply Subtype.ext
    rfl

def subspaceInverse (s : Set X) : (inSubset s : SSet) ⟶ singularSet s where
  app n := TypeCat.ofHom fun σ =>
    (TopCat.toSSetObjEquiv (TopCat.of s) n).symm
      ⟨fun p => ⟨TopCat.toSSetObjEquiv (TopCat.of X) n σ.val p, σ.property p⟩,
        (TopCat.toSSetObjEquiv (TopCat.of X) n σ.val).continuous.subtype_mk _⟩
  naturality {n m} f := by
    ext σ
    rfl

def subspaceIso (s : Set X) : singularSet s ≅ (inSubset s : SSet) where
  hom := subspaceMap s
  inv := subspaceInverse s
  hom_inv_id := by
    ext n σ
    rfl
  inv_hom_id := by
    ext n σ
    apply Subtype.ext
    rfl

def subspaceHomologyIso (s : Set X) (n : ℕ) :
    RealSingularHomology n s ≅
      (inSubset s : SSet).homology (ModuleCat.of ℝ ℝ) n :=
  (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso (subspaceIso s)

theorem subspace_homology_subsingleton (s : Set X) [ContractibleSpace s]
    (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((inSubset s : SSet).homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  let := realSingularHomology_subsingleton_of_contractible n hn s
  exact (subspaceHomologyIso s n).toLinearEquiv.symm.injective.subsingleton

end Problem340.SingularSmallChains

end

end OAI
