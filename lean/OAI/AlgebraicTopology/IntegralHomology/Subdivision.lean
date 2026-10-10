import OAI.AlgebraicTopology.IntegralHomology.Simplex

namespace OAI

noncomputable section

namespace Kaplansky

/-! Singular subdivision, small-chain homotopies, and iterated mesh bounds. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

section
variable {κ : Type}

/-- The ambient convex hull of a tuple's vertices. -/
def simplexTupleHull {n : ℕ} (v : Fin (n+1) → StdSimplex ℝ κ) : Set (κ → ℝ) :=
  convexHull ℝ (Set.range (fun index => ⇑(v index).weights))

theorem simplexTupleHull_vertex {n : ℕ} (v : Fin (n+1) → StdSimplex ℝ κ) (i : Fin (n+1)) :
    ⇑(v i).weights ∈ simplexTupleHull v := subset_convexHull ℝ _ (Set.mem_range_self i)

theorem simplexTupleHull_face {n : ℕ} (v : Fin (n+2) → StdSimplex ℝ κ) (i : Fin (n+2)) :
    simplexTupleHull (v ∘ i.succAbove) ⊆ simplexTupleHull v := by
  apply convexHull_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨i.succAbove j, rfl⟩

variable [Fintype κ]

theorem simplexTupleCenter_mem_hull {n : ℕ} (v : Fin (n+2) → StdSimplex ℝ κ) :
    ⇑(simplexTupleCenter n v).weights ∈ simplexTupleHull v := by
  simp only [simplexTupleCenter, simplexCombination_coe]
  apply (convex_convexHull ℝ _).sum_mem
  · intro index _
    exact (StdSimplex.barycenter (K := ℝ) (M := Fin (n+2))).weights_nonneg index
  · exact (StdSimplex.barycenter (K := ℝ) (M := Fin (n+2))).total_of_fintype
  · intro index _
    exact simplexTupleHull_vertex v index

/-- The barycenter contraction estimate holds on the entire old convex hull. -/
theorem simplexTupleCenter_hull_dist_le {n : ℕ} (v : Fin (n+2) → StdSimplex ℝ κ)
    (D : ℝ) (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x : StdSimplex ℝ κ) (hx : ⇑x.weights ∈ simplexTupleHull v) :
    dist (simplexTupleCenter n v) x ≤ ((n+1 : ℝ)/(n+2))*D := by
  have hs : simplexTupleHull v ⊆
      Metric.closedBall ⇑(simplexTupleCenter n v).weights (((n+1 : ℝ)/(n+2))*D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact simplexTupleCenter_vertex_dist_le n v D hv i
  exact (dist_comm _ _).le.trans (hs hx)

/-- Support condition recording both the original hull and the new mesh. -/
def tupleHullMesh {n m : ℕ} (v : Fin (n+1) → StdSimplex ℝ κ) (D : ℝ)
    (w : Fin (m+1) → StdSimplex ℝ κ) : Prop :=
  (∀ i, ⇑(w i).weights ∈ simplexTupleHull v) ∧ ∀ i j, dist (w i) (w j) ≤ D

/-- Every simplex in one barycentric subdivision has mesh at most n/(n+1)
times the old vertex mesh. Support is expressed in the actual free chain group. -/
theorem tupleSubdivision_mesh (n : ℕ) (v : Fin (n+1) → StdSimplex ℝ κ)
    (D : ℝ) (hD : 0 ≤ D) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    tupleSubdivisionMap simplexTupleCenter n (tupleGen v (1 : ℤ)) ∈
      tupleChainSpan (tupleHullMesh v (((n : ℝ)/(n+1))*D)) := by
  induction n with
  | zero =>
    rw [tupleSubdivisionMap_zero]
    apply tupleGen_mem_span
    constructor
    · exact simplexTupleHull_vertex v
    · intro i j
      have he : i = j := Fin.ext (by omega)
      simp [he]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    rw [tupleSubdivision_gen_value]
    apply Submodule.sum_mem
    intro i hi
    refine (tupleChainSpan (tupleHullMesh v (((n+1 : ℝ)/(n+2))*D))).toAddSubgroup.zsmul_mem ?_ ((-1 : ℤ)^i.val)
    apply tupleCone_mem_span (simplexTupleCenter n v) (P := tupleHullMesh (v ∘ i.succAbove) (((n : ℝ)/(n+1))*D))
      (fun w hw => ?_) (ih (v ∘ i.succAbove) (fun a b => hv _ _))
    constructor
    · intro j
      cases j using Fin.cases with
      | zero => exact simplexTupleCenter_mem_hull v
      | succ j => exact simplexTupleHull_face v i (hw.1 j)
    · have hfactor : ((n : ℝ)/(n+1))*D ≤ ((n+1 : ℝ)/(n+2))*D := by
        apply mul_le_mul_of_nonneg_right _ hD
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      intro a b
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => simp only [dist_self]; positivity
        | succ b =>
          exact simplexTupleCenter_hull_dist_le v D hv (w b) (simplexTupleHull_face v i (hw.1 b))
      | succ a =>
        cases b using Fin.cases with
        | zero =>
          rw [dist_comm]
          exact simplexTupleCenter_hull_dist_le v D hv (w a) (simplexTupleHull_face v i (hw.1 a))
        | succ b => exact (hw.2 a b).trans hfactor

end

section

/-- The actual map represented by a singular simplex, with unlifted domain. -/
def singularSimplexTopMap {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : standardSimplexSpace n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquiv X _ σ)

@[reassoc (attr := simp)]
theorem singularGen_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ (integralSingularChains.map f).f n =
      singularGen ((TopCat.toSSet.map f).app _ σ) :=
  SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of ℤ ℤ) (x := σ)

@[reassoc]
theorem singularGen_boundary {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    singularGen σ ≫ (integralSingularChains.obj X).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • singularGen ((TopCat.toSSet.obj X).δ i σ) :=
  SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) (x := σ)

@[simp]
theorem singularSimplexTopMap_face {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) (i : Fin (n+2)) :
    singularSimplexTopMap ((TopCat.toSSet.obj X).δ i σ) =
      standardSimplexMap i.succAbove ≫ singularSimplexTopMap σ := rfl

@[simp]
theorem singularSimplexTopMap_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexTopMap ((TopCat.toSSet.map f).app _ σ) = singularSimplexTopMap σ ≫ f := rfl

@[reassoc (attr := simp)]
theorem singularGen_identity_map {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen (singularSimplexOfMap (ContinuousMap.id _)) ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f n = singularGen σ := by
  rw [singularGen_map]
  congr 1

/-- Barycentric subdivision on the existing integral singular chains. -/
def singularSubdivisionMap (X : TopCat.{0}) (n : ℕ) :
    (integralSingularChains.obj X).X n ⟶ (integralSingularChains.obj X).X n :=
  Sigma.desc (fun σ => universalSubdivision n ≫
    (integralSingularChains.map (singularSimplexTopMap σ)).f n)

@[reassoc (attr := simp)]
theorem singularGen_subdivision {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ singularSubdivisionMap X n = universalSubdivision n ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f n := by
  exact Sigma.ι_comp_desc _ _

@[reassoc]
theorem singularSubdivisionMap_d (X : TopCat.{0}) (n : ℕ) :
    singularSubdivisionMap X (n+1) ≫ (integralSingularChains.obj X).d (n+1) n =
      (integralSingularChains.obj X).d (n+1) n ≫ singularSubdivisionMap X n := by
  apply singularChains_hom_ext
  intro σ
  rw [← Category.assoc, singularGen_subdivision, Category.assoc,
    (integralSingularChains.map (singularSimplexTopMap σ)).comm,
    ← Category.assoc, universalSubdivision_boundary]
  rw [← Category.assoc, singularGen_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, singularGen_subdivision,
    singularSimplexTopMap_face, Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]

/-- Constructed chain endomorphism, with no subdivision or excision hypothesis. -/
def singularSubdivision (X : TopCat.{0}) :
    integralSingularChains.obj X ⟶ integralSingularChains.obj X :=
  ChainComplex.ofHom (singularSubdivisionMap X) (singularSubdivisionMap_d X)

@[reassoc]
theorem singularSubdivision_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    integralSingularChains.map f ≫ singularSubdivision Y =
      singularSubdivision X ≫ integralSingularChains.map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply singularChains_hom_ext
  intro σ
  change singularGen σ ≫ (integralSingularChains.map f).f n ≫ singularSubdivisionMap Y n =
    singularGen σ ≫ singularSubdivisionMap X n ≫ (integralSingularChains.map f).f n
  simp only [singularGen_map_assoc, singularGen_subdivision, singularGen_subdivision_assoc,
    singularSimplexTopMap_map, Functor.map_comp, HomologicalComplex.comp_f]

/-- The universal prism transported along each actual singular simplex. -/
def singularSubdivisionPrism (X : TopCat.{0}) (n : ℕ) :
    (integralSingularChains.obj X).X n ⟶ (integralSingularChains.obj X).X (n+1) :=
  Sigma.desc (fun σ => universalSubdivisionPrism n ≫
    (integralSingularChains.map (singularSimplexTopMap σ)).f (n+1))

@[reassoc (attr := simp)]
theorem singularGen_prism {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ singularSubdivisionPrism X n = universalSubdivisionPrism n ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f (n+1) := by
  exact Sigma.ι_comp_desc _ _

@[simp]
theorem singularSubdivisionPrism_zero (X : TopCat.{0}) : singularSubdivisionPrism X 0 = 0 := by
  apply singularChains_hom_ext
  intro σ
  rw [singularGen_prism, universalSubdivisionPrism_zero]
  simp only [zero_comp, comp_zero]

@[simp]
theorem singularSubdivisionMap_zero (X : TopCat.{0}) : singularSubdivisionMap X 0 = 𝟙 _ := by
  apply singularChains_hom_ext
  intro σ
  rw [singularGen_subdivision, universalSubdivision_zero, singularGen_identity_map]
  exact (Category.comp_id _).symm

/-- The chain homotopy equation on actual singular chains in all positive degrees. -/
theorem singularSubdivisionPrism_equation (X : TopCat.{0}) (n : ℕ) :
    singularSubdivisionPrism X (n+1) ≫ (integralSingularChains.obj X).d (n+2) (n+1) =
      𝟙 _ - singularSubdivisionMap X (n+1) -
      (integralSingularChains.obj X).d (n+1) n ≫ singularSubdivisionPrism X n := by
  apply singularChains_hom_ext
  intro σ
  rw [← Category.assoc, singularGen_prism, Category.assoc,
    (integralSingularChains.map (singularSimplexTopMap σ)).comm,
    ← Category.assoc, universalSubdivisionPrism_boundary]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    singularGen_identity_map, singularGen_subdivision]
  congr 1
  rw [← Category.assoc, singularGen_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, singularGen_prism,
    singularSimplexTopMap_face, Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]

/-- An explicit homotopy between the identity and barycentric subdivision. -/
def singularSubdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (𝟙 (integralSingularChains.obj X)) (singularSubdivision X) :=
  chainHomotopyOfComponents _ _ (singularSubdivisionPrism X)
    (by simp [singularSubdivision]) (fun n => by
      change 𝟙 _ = _ + _ + singularSubdivisionMap X (n+1)
      rw [singularSubdivisionPrism_equation]
      abel)

@[reassoc]
theorem singularSubdivisionPrism_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (integralSingularChains.map f).f n ≫ singularSubdivisionPrism Y n =
      singularSubdivisionPrism X n ≫ (integralSingularChains.map f).f (n+1) := by
  apply singularChains_hom_ext
  intro σ
  simp only [singularGen_map_assoc, singularGen_prism, singularGen_prism_assoc,
    singularSimplexTopMap_map, Functor.map_comp, HomologicalComplex.comp_f]

/-- Subdivision acts as the identity on actual integral singular homology. -/
theorem singularSubdivision_homologyMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (singularSubdivision X) n = 𝟙 _ := by
  rw [← (singularSubdivisionHomotopy X).homologyMap_eq, HomologicalComplex.homologyMap_id]

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Every singular simplex inside the image of a small simplex remains small.
The statement uses the entire simplex image, so it also controls the prism. -/
theorem smallSimplex_carrier {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    SSet.Subcomplex.range (TopCat.toSSet.map (singularSimplexTopMap σ.val)) ≤
      singularSubset U ⊔ singularSubset V := by
  intro m τ hτ
  obtain ⟨η, rfl⟩ := hτ
  have hσ := (mem_smallSingularSet_iff U V _ σ.val).mp σ.property
  rw [mem_smallSingularSet_iff]
  rcases hσ with hσ | hσ
  · left
    intro p
    exact hσ (ULift.up (singularSimplexMap m η p))
  · right
    intro p
    exact hσ (ULift.up (singularSimplexMap m η p))

def smallSimplexCarrier {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    TopCat.toSSet.obj (standardSimplexSpace n) ⟶ smallSingularSet U V :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularSimplexTopMap σ.val))
    (smallSimplex_carrier U V σ)

def smallSimplexChains {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    integralSingularChains.obj (standardSimplexSpace n) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (smallSimplexCarrier U V σ)

@[reassoc (attr := simp)]
theorem smallSimplexChains_inclusion {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSimplexChains U V σ ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (singularSimplexTopMap σ.val) := by
  erw [smallSimplexChains, smallSingularChainInclusion, ← Functor.map_comp]
  rfl

abbrev smallSingularGen {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (smallSingularChains U V).X n :=
  (smallSingularSet U V).ιChainComplex σ

/-- Maps from small chains are determined by their values on small singular simplices. -/
theorem smallSingularChains_hom_ext {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (smallSingularChains U V).X n ⟶ T}
    (h : ∀ σ : (smallSingularSet U V) _⦋n⦌,
      smallSingularGen U V σ ≫ f = smallSingularGen U V σ ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

@[reassoc (attr := simp)]
theorem smallSingularGen_inclusion {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ (smallSingularChainInclusion U V).f n = singularGen σ.val :=
  SSet.ι_chainComplexMap_f (X := smallSingularSet U V) (Y := TopCat.toSSet.obj _)
    (f := (singularSubset U ⊔ singularSubset V).ι) (R := ModuleCat.of ℤ ℤ) (x := σ)

/-- Subdivision restricted to the actual small chain groups. -/
def smallSubdivisionMap (n : ℕ) : (smallSingularChains U V).X n ⟶ (smallSingularChains U V).X n :=
  Sigma.desc (fun σ => universalSubdivision n ≫ (smallSimplexChains U V σ).f n)

/-- The prism restricted to the same small chain groups. -/
def smallSubdivisionPrism (n : ℕ) :
    (smallSingularChains U V).X n ⟶ (smallSingularChains U V).X (n+1) :=
  Sigma.desc (fun σ => universalSubdivisionPrism n ≫ (smallSimplexChains U V σ).f (n+1))

@[reassoc (attr := simp)]
theorem smallGen_subdivision {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ smallSubdivisionMap U V n =
      universalSubdivision n ≫ (smallSimplexChains U V σ).f n := by
  exact Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem smallGen_prism {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ smallSubdivisionPrism U V n =
      universalSubdivisionPrism n ≫ (smallSimplexChains U V σ).f (n+1) := by
  exact Sigma.ι_comp_desc _ _

@[reassoc]
theorem smallSubdivisionMap_inclusion (n : ℕ) :
    smallSubdivisionMap U V n ≫ (smallSingularChainInclusion U V).f n =
      (smallSingularChainInclusion U V).f n ≫ singularSubdivisionMap (TopCat.of X) n := by
  apply smallSingularChains_hom_ext
  intro σ
  rw [← Category.assoc, smallGen_subdivision, Category.assoc]
  have h := congrArg (fun f => f.f n) (smallSimplexChains_inclusion U V σ)
  change _ ≫ _ = _ at h
  rw [h, smallSingularGen_inclusion_assoc, singularGen_subdivision]

@[reassoc]
theorem smallSubdivisionPrism_inclusion (n : ℕ) :
    smallSubdivisionPrism U V n ≫ (smallSingularChainInclusion U V).f (n+1) =
      (smallSingularChainInclusion U V).f n ≫ singularSubdivisionPrism (TopCat.of X) n := by
  apply smallSingularChains_hom_ext
  intro σ
  rw [← Category.assoc, smallGen_prism, Category.assoc]
  have h := congrArg (fun f => f.f (n+1)) (smallSimplexChains_inclusion U V σ)
  change _ ≫ _ = _ at h
  rw [h, smallSingularGen_inclusion_assoc, singularGen_prism]

/-- The restriction remains a chain map, proved by injectivity of inclusion. -/
theorem smallSubdivisionMap_d (n : ℕ) :
    smallSubdivisionMap U V (n+1) ≫ (smallSingularChains U V).d (n+1) n =
      (smallSingularChains U V).d (n+1) n ≫ smallSubdivisionMap U V n := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f n)).mp
  simp only [Category.assoc, ← (smallSingularChainInclusion U V).comm_assoc,
    ← (smallSingularChainInclusion U V).comm, smallSubdivisionMap_inclusion,
    smallSubdivisionMap_inclusion_assoc, singularSubdivisionMap_d]

def smallSubdivision : smallSingularChains U V ⟶ smallSingularChains U V :=
  ChainComplex.ofHom (smallSubdivisionMap U V) (smallSubdivisionMap_d U V)

end

section

/-- Composition of affine interpolations is affine interpolation of the images. -/
theorem simplexCombination_assoc {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (w : κ → StdSimplex ℝ μ) (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) :
    simplexCombination w (simplexCombination v t) =
      simplexCombination (simplexCombination w ∘ v) t := by
  exact (iConvexComb_assoc t v w).symm

@[simp]
theorem simplexTupleCenter_combination {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → StdSimplex ℝ κ) (n : ℕ) (v : Fin (n+2) → StdSimplex ℝ ι) :
    simplexCombination w (simplexTupleCenter n v) =
      simplexTupleCenter n (simplexCombination w ∘ v) :=
  simplexCombination_assoc w v _

/-- Naturality of interpolation for all affine simplex maps, not only cofaces. -/
theorem simplexAffineChains_combination {k l : ℕ}
    (v : Fin (k+1) → StdSimplex ℝ (Fin (l+1))) :
    tupleChainMap (simplexCombination v) ≫ simplexAffineChains l =
      simplexAffineChains k ≫ integralSingularChains.map (TopCat.ofHom (simplexCombinationMap v)) := by
  have hs : tupleSSetMap (simplexCombination v) ≫ simplexAffineSSet l =
      simplexAffineSSet k ≫ TopCat.toSSet.map (TopCat.ofHom (simplexCombinationMap v)) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro w
    apply (TopCat.toSSetObjEquiv _ n).injective
    apply ContinuousMap.ext
    intro t
    change simplexCombination (simplexCombination v ∘ w) t = simplexCombination v (simplexCombination w t)
    exact (simplexCombination_assoc v w t).symm
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ =
    integralSimplicialChains.map _ ≫ integralSimplicialChains.map _
  rw [← Functor.map_comp, ← Functor.map_comp, hs]

/-- Interpolation intertwines tuple subdivision with singular subdivision.
This is needed for iterating the geometric mesh estimate. -/
theorem simplexAffineChains_subdivision (k : ℕ) :
    simplexAffineChains k ≫ singularSubdivision (standardSimplexSpace k) =
      tupleSubdivision simplexTupleCenter ≫ simplexAffineChains k := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply tupleChains_hom_ext
  intro v
  change tupleGen v ≫ (simplexAffineChains k).f n ≫ singularSubdivisionMap _ n =
    tupleGen v ≫ tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains k).f n
  rw [tupleGen_affine_assoc, singularGen_subdivision]
  change universalSubdivision n ≫
    (integralSingularChains.map (TopCat.ofHom (simplexCombinationMap v))).f n = _
  unfold universalSubdivision simplexSubdivisionChains
  change (tupleGen StdSimplex.single ≫ tupleSubdivisionMap simplexTupleCenter n ≫
    (simplexAffineChains n).f n) ≫ _ = _
  have ha := congrArg (fun f => f.f n) (simplexAffineChains_combination v)
  change _ ≫ _ = _ ≫ _ at ha
  simp only [Category.assoc]
  rw [← ha, ← Category.assoc (tupleSubdivisionMap simplexTupleCenter n),
    tupleSubdivisionMap_naturality _ _ _ (simplexTupleCenter_combination v)]
  simp only [Category.assoc, tupleGen_map_assoc]
  have hv : simplexCombination v ∘ StdSimplex.single = v := by
    funext i
    exact simplexCombination_vertex v i
  rw [hv]

variable {X : Type} [TopologicalSpace X] (U V : Set X)

@[simp]
theorem smallSubdivisionMap_zero : smallSubdivisionMap U V 0 = 𝟙 _ := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f 0)).mp
  rw [smallSubdivisionMap_inclusion, singularSubdivisionMap_zero]
  simp only [Category.comp_id, Category.id_comp]

@[simp]
theorem smallSubdivisionPrism_zero : smallSubdivisionPrism U V 0 = 0 := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f 1)).mp
  rw [smallSubdivisionPrism_inclusion, singularSubdivisionPrism_zero]
  simp only [zero_comp, comp_zero]

/-- The homotopy equation also holds before inclusion into full chains. -/
theorem smallSubdivisionPrism_equation (n : ℕ) :
    smallSubdivisionPrism U V (n+1) ≫ (smallSingularChains U V).d (n+2) (n+1) =
      𝟙 _ - smallSubdivisionMap U V (n+1) -
      (smallSingularChains U V).d (n+1) n ≫ smallSubdivisionPrism U V n := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f (n+1))).mp
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    ← (smallSingularChainInclusion U V).comm,
    smallSubdivisionPrism_inclusion_assoc, smallSubdivisionMap_inclusion,
    smallSubdivisionPrism_inclusion, singularSubdivisionPrism_equation,
    Preadditive.comp_sub, Category.comp_id]
  rw [(smallSingularChainInclusion U V).comm_assoc]

def smallSubdivisionHomotopy : Homotopy (𝟙 (smallSingularChains U V)) (smallSubdivision U V) :=
  chainHomotopyOfComponents _ _ (smallSubdivisionPrism U V)
    (by simp [smallSubdivision]) (fun n => by
      change 𝟙 _ = _ + _ + smallSubdivisionMap U V (n+1)
      rw [smallSubdivisionPrism_equation]
      abel)

/-- Small-chain subdivision induces the identity on homology, without any
cover hypothesis. Comparison to full homology still needs eventual smallness. -/
theorem smallSubdivision_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivision U V) n = 𝟙 _ := by
  rw [← (smallSubdivisionHomotopy U V).homologyMap_eq, HomologicalComplex.homologyMap_id]

@[reassoc]
theorem smallSubdivision_inclusion :
    smallSubdivision U V ≫ smallSingularChainInclusion U V =
      smallSingularChainInclusion U V ≫ singularSubdivision (TopCat.of X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact smallSubdivisionMap_inclusion U V n

end

variable {κ : Type} [Fintype κ]

def tupleMeshSpan (n : ℕ) (D : ℝ) :
    Submodule ℤ ((tupleChains (StdSimplex ℝ κ)).X n) :=
  tupleChainSpan (fun v => ∀ i j, dist (v i) (v j) ≤ D)

/-- Subdivision contracts the mesh of an arbitrary supported affine chain. -/
theorem tupleSubdivision_mem_mesh {n : ℕ} (D : ℝ) (hD : 0 ≤ D)
    {c : (tupleChains (StdSimplex ℝ κ)).X n} (hc : c ∈ tupleMeshSpan n D) :
    tupleSubdivisionMap simplexTupleCenter n c ∈ tupleMeshSpan n (((n : ℝ)/(n+1))*D) := by
  refine tupleChainSpan_map (tupleSubdivisionMap simplexTupleCenter n) (fun v hv => ?_) hc
  exact tupleChainSpan_mono (fun w hw => hw.2) (tupleSubdivision_mesh n v D hD hv)

/-- Actual geometric decay for every iterated barycentric subdivision,
including repeated or degenerate vertices and the degree-zero case. -/
theorem tupleSubdivision_iterate_mesh {n : ℕ} (D : ℝ) (hD : 0 ≤ D)
    {c : (tupleChains (StdSimplex ℝ κ)).X n} (hc : c ∈ tupleMeshSpan n D) (k : ℕ) :
    (tupleSubdivisionMap simplexTupleCenter n)^[k] c ∈
      tupleMeshSpan n (D * ((n : ℝ)/(n+1))^k) := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, mul_one] using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := tupleSubdivision_mem_mesh (D * ((n : ℝ)/(n+1))^k) (by positivity) ih
    convert h using 1
    ring_nf

/-- The universal vertex tuple starts with mesh at most one in the actual
sup metric of the library's standard simplex. -/
theorem simplexVertices_mem_mesh (n : ℕ) :
    tupleGen (StdSimplex.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ) ∈
      tupleMeshSpan n 1 := by
  apply tupleGen_mem_span
  intro i j
  change dist (⇑(StdSimplex.single (R := ℝ) i).weights)
    (⇑(StdSimplex.single (R := ℝ) j).weights) ≤ 1
  apply (dist_pi_le_iff (by norm_num)).mpr
  intro index
  simp only [StdSimplex.weights_single, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- Geometric mesh estimate for the universal subdivided simplex. -/
theorem universalTupleSubdivision_mesh (n k : ℕ) :
    (tupleSubdivisionMap simplexTupleCenter n)^[k]
      (tupleGen (StdSimplex.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ)) ∈
      tupleMeshSpan n (((n : ℝ)/(n+1))^k) := by
  simpa only [one_mul] using tupleSubdivision_iterate_mesh 1 (by norm_num) (simplexVertices_mem_mesh n) k

/-- The mesh factor is strictly less than one in every fixed degree. -/
theorem simplexMeshFactor_lt_one (n : ℕ) : (n : ℝ)/(n+1) < 1 := by
  apply (div_lt_one (by positivity)).mpr
  linarith

end

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity
section

/-- Iteration on an actual singular simplex agrees with the constructed
iterated affine subdivision inside its domain. -/
theorem singularSubdivision_iterate_gen {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (k : ℕ) :
    (singularSubdivisionMap X n)^[k] (singularGen σ (1 : ℤ)) =
      (integralSingularChains.map (singularSimplexTopMap σ)).f n
        ((simplexAffineChains n).f n
          ((tupleSubdivisionMap simplexTupleCenter n)^[k]
            (tupleGen (StdSimplex.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ)))) := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply]
    have h := tupleGen_vertices_affine n
    have h' := singularGen_identity_map σ
    exact (ConcreteCategory.congr_hom (by
      rw [← Category.assoc, h]
      exact h' : tupleGen StdSimplex.single ≫ (simplexAffineChains n).f n ≫
        (integralSingularChains.map (singularSimplexTopMap σ)).f n = singularGen σ) (1 : ℤ)).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have h := congrArg (fun f => f.f n) (simplexAffineChains_subdivision n)
    have h' := congrArg (fun f => f.f n) (singularSubdivision_naturality (singularSimplexTopMap σ))
    change (simplexAffineChains n).f n ≫ singularSubdivisionMap _ n =
      tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains n).f n at h
    change (integralSingularChains.map (singularSimplexTopMap σ)).f n ≫ singularSubdivisionMap X n =
      singularSubdivisionMap _ n ≫ (integralSingularChains.map (singularSimplexTopMap σ)).f n at h'
    rw [← ModuleCat.comp_apply, h', ModuleCat.comp_apply,
      ← ModuleCat.comp_apply ((simplexAffineChains n).f n), h, ModuleCat.comp_apply]

/-- A singular generator that is small belongs to the actual image of the
small-chain inclusion. -/
theorem small_singularGen_mem_range {X : Type} [TopologicalSpace X] (U V : Set X)
    {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (hσ : σ ∈ (singularSubset U ⊔ singularSubset V).obj (Opposite.op ⦋n⦌)) :
    singularGen σ (1 : ℤ) ∈ LinearMap.range ((smallSingularChainInclusion U V).f n).hom := by
  refine ⟨smallSingularGen U V ⟨σ, hσ⟩ (1 : ℤ), ?_⟩
  exact ConcreteCategory.congr_hom (smallSingularGen_inclusion U V ⟨σ, hσ⟩) (1 : ℤ)

end

end Kaplansky

end

end OAI
