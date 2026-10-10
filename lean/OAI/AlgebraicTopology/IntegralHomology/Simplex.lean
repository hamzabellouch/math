import OAI.AlgebraicTopology.IntegralHomology.TupleChains
import Mathlib.Analysis.Convex.StdSimplex

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine simplex chains, mesh geometry, and universal subdivision. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

instance simplexMetricSpace {κ : Type} [Fintype κ] : MetricSpace (StdSimplex ℝ κ) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun point : StdSimplex ℝ κ => (point.weights : κ → ℝ))
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ κ)

/-- Affine interpolation of vertices in an actual standard simplex. -/
def simplexCombination {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) : StdSimplex ℝ κ :=
  t.iConvexComb v

@[simp]
theorem simplexCombination_coe {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) :
    ⇑(simplexCombination v t).weights = ∑ index, t.weights index • ⇑(v index).weights := by
  classical
  simp [simplexCombination, iConvexComb, StdSimplex.weights_sConvexComb,
    StdSimplex.weights_map, Finsupp.sum_mapDomain_index, add_smul,
    Finsupp.sum_fintype, Finsupp.coe_finsetSum, Finsupp.coe_smul]

/-- Interpolation is continuous in the barycentric coordinates. -/
def simplexCombinationMap {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → StdSimplex ℝ κ) : C(StdSimplex ℝ ι, StdSimplex ℝ κ) :=
  ⟨simplexCombination v, by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).continuous_iff.mpr
    change Continuous (fun point => ⇑(simplexCombination v point).weights)
    simp only [simplexCombination_coe]
    apply continuous_finsetSum
    intro index _
    exact (StdSimplex.continuous_weights_apply ℝ index).smul continuous_const⟩

@[simp]
theorem simplexCombination_vertex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (v : ι → StdSimplex ℝ κ) (i : ι) :
    simplexCombination v (StdSimplex.single i) = v i := by
  exact Convexity.iConvexComb_single i v

@[simp]
theorem simplexCombination_vertices {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : StdSimplex ℝ ι) : simplexCombination StdSimplex.single t = t := by
  exact StdSimplex.iConvexComb_single t

/-- Interpolation intertwines vertex reindexing with the genuine
standard-simplex map, including all cofaces. -/
theorem simplexCombination_reindex {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : κ → StdSimplex ℝ μ) (f : ι → κ) (t : StdSimplex ℝ ι) :
    simplexCombination (v ∘ f) t = simplexCombination v (StdSimplex.map f t) := by
  exact (Convexity.iConvexComb_map t f v).symm

/-- Affine maps of the target simplex commute with interpolation. -/
theorem simplexCombination_map {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : ι → StdSimplex ℝ κ) (f : κ → μ) (t : StdSimplex ℝ ι) :
    StdSimplex.map f (simplexCombination v t) =
      simplexCombination (StdSimplex.map f ∘ v) t := by
  exact Convexity.map_iConvexComb t v

/-- Barycenter of a tuple in the ambient standard simplex. -/
def simplexTupleCenter {κ : Type} [Fintype κ] (n : ℕ)
    (v : Fin (n+2) → StdSimplex ℝ κ) : StdSimplex ℝ κ :=
  simplexCombination v StdSimplex.barycenter

@[simp]
theorem simplexTupleCenter_map {κ μ : Type} [Fintype κ] [Fintype μ]
    (f : κ → μ) (n : ℕ) (v : Fin (n+2) → StdSimplex ℝ κ) :
    StdSimplex.map f (simplexTupleCenter n v) =
      simplexTupleCenter n (StdSimplex.map f ∘ v) :=
  simplexCombination_map v f _

/-- A convex combination stays within any common distance bound from a point. -/
theorem simplexCombination_dist_le {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) (p : StdSimplex ℝ κ)
    (D : ℝ) (hv : ∀ i, dist (v i) p ≤ D) :
    dist (simplexCombination v t) p ≤ D := by
  have he : ⇑(simplexCombination v t).weights - ⇑p.weights =
      ∑ i, t.weights i • (⇑(v i).weights - ⇑p.weights) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, t.total_of_fintype, one_smul,
      simplexCombination_coe]
  change ‖⇑(simplexCombination v t).weights - ⇑p.weights‖ ≤ D
  rw [he]
  calc
    ‖∑ i, t.weights i • (⇑(v i).weights - ⇑p.weights)‖ ≤
      ∑ i, ‖t.weights i • (⇑(v i).weights - ⇑p.weights)‖ := norm_sum_le _ _
    _ = ∑ i, t.weights i * dist (v i) p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (t.weights_nonneg i)]
      rfl
    _ ≤ ∑ i, t.weights i * D :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (t.weights_nonneg i))
    _ = D := by rw [← Finset.sum_mul, t.total_of_fintype, one_mul]

/-- Affine interpolation cannot increase a bound on pairwise vertex distances. -/
theorem simplexCombination_pair_dist_le {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → StdSimplex ℝ κ) (s t : StdSimplex ℝ ι)
    (D : ℝ) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (simplexCombination v s) (simplexCombination v t) ≤ D := by
  apply simplexCombination_dist_le
  intro i
  rw [dist_comm]
  exact simplexCombination_dist_le v t (v i) D (fun j => hv j i)

/-- Averaging N vertices has distance at most (N-1)/N times the original
mesh from every vertex. This includes repeated vertices. -/
theorem simplexTupleCenter_vertex_dist_le {κ : Type} [Fintype κ]
    (n : ℕ) (v : Fin (n+2) → StdSimplex ℝ κ) (D : ℝ)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) (j : Fin (n+2)) :
    dist (simplexTupleCenter n v) (v j) ≤ ((n+1 : ℝ) / (n+2)) * D := by
  have hn : (0 : ℝ) < n+2 := by positivity
  have he : ⇑(simplexTupleCenter n v).weights - ⇑(v j).weights =
      (n+2 : ℝ)⁻¹ • ∑ i, (⇑(v i).weights - ⇑(v j).weights) := by
    simp only [simplexTupleCenter, simplexCombination_coe, StdSimplex.weights_barycenter_apply, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, smul_sub,
      Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [ne_of_gt hn]
  change ‖⇑(simplexTupleCenter n v).weights - ⇑(v j).weights‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have hsum : ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤ (n+1 : ℝ) * D := by
    calc
      ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤
        ∑ i, ‖⇑(v i).weights - ⇑(v j).weights‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n+2), if i = j then 0 else D := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : i = j
        · subst i; simp
        · have distance_bound : ‖⇑(v i).weights - ⇑(v j).weights‖ ≤ D := hv i j
          simpa [h] using distance_bound
      _ = (n+1 : ℝ) * D := by
        have hh (i : Fin (n+2)) : (if i = j then 0 else D) = D - (if i = j then D else 0) := by
          split_ifs <;> simp
        simp_rw [hh]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
        ring
  calc
    (n+2 : ℝ)⁻¹ * ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤ (n+2 : ℝ)⁻¹ * ((n+1) * D) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = _ := by ring

/-- Every point of the old affine simplex is close to its barycenter with
the strict dimension-dependent contraction factor. -/
theorem simplexTupleCenter_combination_dist_le {κ : Type} [Fintype κ]
    (n : ℕ) (v : Fin (n+2) → StdSimplex ℝ κ) (t : StdSimplex ℝ (Fin (n+2)))
    (D : ℝ) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (simplexTupleCenter n v) (simplexCombination v t) ≤ ((n+1 : ℝ) / (n+2)) * D := by
  rw [dist_comm]
  exact simplexCombination_dist_le v t _ _ (fun i => by
    rw [dist_comm]
    exact simplexTupleCenter_vertex_dist_le n v D hv i)

abbrev standardSimplexSpace (k : ℕ) : TopCat.{0} :=
  TopCat.of (StdSimplex ℝ (Fin (k+1)))

/-- A continuous simplex as an element of the library singular set. -/
def singularSimplexOfMap {X : TopCat.{0}} {n : ℕ}
    (f : C(StdSimplex ℝ (Fin (n+1)), X)) : (TopCat.toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv X _).symm f

abbrev singularGen {X : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (integralSingularChains.obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex σ

/-- Maps from singular chains are determined by their values on singular simplices. -/
theorem singularChains_hom_ext {X : TopCat.{0}} {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (integralSingularChains.obj X).X n ⟶ T}
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, singularGen σ ≫ f = singularGen σ ≫ g) :
    f = g := SSet.chainComplex_hom_ext h

/-- Interpolation into actual singular simplices, in every degree. -/
def simplexAffineSSet (k : ℕ) :
    tupleSSet (StdSimplex ℝ (Fin (k+1))) ⟶ TopCat.toSSet.obj (standardSimplexSpace k) where
  app n := ↾fun v => singularSimplexOfMap (simplexCombinationMap v)
  naturality {a b} f := by
    apply ConcreteCategory.hom_ext
    intro v
    apply (TopCat.toSSetObjEquiv _ b).injective
    apply ContinuousMap.ext
    intro t
    change simplexCombination (v ∘ f.unop.toOrderHom) t =
      simplexCombination v (StdSimplex.map f.unop.toOrderHom t)
    exact simplexCombination_reindex v f.unop.toOrderHom t

abbrev simplexAffineChains (k : ℕ) :
    tupleChains (StdSimplex ℝ (Fin (k+1))) ⟶
      integralSingularChains.obj (standardSimplexSpace k) :=
  SSet.chainComplexMap (simplexAffineSSet k) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem tupleGen_affine {k n : ℕ} (v : Fin (n+1) → StdSimplex ℝ (Fin (k+1))) :
    tupleGen v ≫ (simplexAffineChains k).f n =
      singularGen (singularSimplexOfMap (simplexCombinationMap v)) :=
  SSet.ι_chainComplexMap_f (X := tupleSSet _) (Y := TopCat.toSSet.obj _)
    (f := simplexAffineSSet k) (R := ModuleCat.of ℤ ℤ) (x := v)

def standardSimplexMap {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    standardSimplexSpace k ⟶ standardSimplexSpace l :=
  TopCat.ofHom ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩

/-- Interpolation is natural in affine maps of ambient simplex coordinates. -/
theorem simplexAffineSSet_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleSSetMap (StdSimplex.map f) ≫ simplexAffineSSet l =
      simplexAffineSSet k ≫ TopCat.toSSet.map (standardSimplexMap f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro v
  apply (TopCat.toSSetObjEquiv _ n).injective
  apply ContinuousMap.ext
  intro t
  change simplexCombination (StdSimplex.map f ∘ v) t =
    StdSimplex.map f (simplexCombination v t)
  exact (simplexCombination_map v f t).symm

@[reassoc]
theorem simplexAffineChains_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleChainMap (StdSimplex.map f) ≫ simplexAffineChains l =
      simplexAffineChains k ≫ integralSingularChains.map (standardSimplexMap f) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ =
    integralSimplicialChains.map _ ≫ integralSimplicialChains.map _
  rw [← Functor.map_comp, ← Functor.map_comp, simplexAffineSSet_naturality]

/-- The identity simplex is the interpolation of its actual vertices. -/
@[reassoc (attr := simp)]
theorem tupleGen_vertices_affine (n : ℕ) :
    tupleGen (StdSimplex.single (R := ℝ) (X := Fin (n+1))) ≫ (simplexAffineChains n).f n =
      singularGen (singularSimplexOfMap (ContinuousMap.id _)) := by
  rw [tupleGen_affine]
  congr 2
  apply ContinuousMap.ext
  intro t
  exact simplexCombination_vertices t

end

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity
section

/-- Barycentric subdivision followed by actual affine singular interpolation. -/
def simplexSubdivisionChains (k : ℕ) :
    tupleChains (StdSimplex ℝ (Fin (k+1))) ⟶
      integralSingularChains.obj (standardSimplexSpace k) :=
  tupleSubdivision simplexTupleCenter ≫ simplexAffineChains k

/-- The corresponding interpolated chain homotopy components. -/
def simplexSubdivisionPrism (k n : ℕ) :
    (tupleChains (StdSimplex ℝ (Fin (k+1)))).X n ⟶
      (integralSingularChains.obj (standardSimplexSpace k)).X (n+1) :=
  tupleSubdivisionPrism simplexTupleCenter n ≫ (simplexAffineChains k).f (n+1)

@[reassoc]
theorem simplexSubdivisionChains_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleChainMap (StdSimplex.map f) ≫ simplexSubdivisionChains l =
      simplexSubdivisionChains k ≫ integralSingularChains.map (standardSimplexMap f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (tupleChainMap (StdSimplex.map f)).f n ≫
      tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains l).f n =
    (tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains k).f n) ≫ _
  rw [← Category.assoc, ← tupleSubdivisionMap_naturality _ _ _ (simplexTupleCenter_map f)]
  rw [Category.assoc]
  have h := congrArg (fun g => g.f n) (simplexAffineChains_naturality f)
  change _ ≫ _ = _ ≫ _ at h
  rw [h, Category.assoc]

@[reassoc]
theorem simplexSubdivisionPrism_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) (n : ℕ) :
    (tupleChainMap (StdSimplex.map f)).f n ≫ simplexSubdivisionPrism l n =
      simplexSubdivisionPrism k n ≫ (integralSingularChains.map (standardSimplexMap f)).f (n+1) := by
  unfold simplexSubdivisionPrism
  rw [← Category.assoc, ← tupleSubdivisionPrism_naturality _ _ _ (simplexTupleCenter_map f)]
  rw [Category.assoc]
  have h := congrArg (fun g => g.f (n+1)) (simplexAffineChains_naturality f)
  change _ ≫ _ = _ ≫ _ at h
  rw [h, Category.assoc]

/-- The subdivided universal identity simplex, as a chain in that same simplex. -/
def universalSubdivision (n : ℕ) : ModuleCat.of ℤ ℤ ⟶
    (integralSingularChains.obj (standardSimplexSpace n)).X n :=
  tupleGen StdSimplex.single ≫ (simplexSubdivisionChains n).f n

def universalSubdivisionPrism (n : ℕ) : ModuleCat.of ℤ ℤ ⟶
    (integralSingularChains.obj (standardSimplexSpace n)).X (n+1) :=
  tupleGen StdSimplex.single ≫ simplexSubdivisionPrism n n

@[reassoc]
theorem universalSubdivision_boundary (n : ℕ) :
    universalSubdivision (n+1) ≫ (integralSingularChains.obj (standardSimplexSpace (n+1))).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (universalSubdivision n ≫ (integralSingularChains.map (standardSimplexMap i.succAbove)).f n) := by
  unfold universalSubdivision
  rw [Category.assoc, (simplexSubdivisionChains (n+1)).comm, ← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have h := congrArg (fun g => g.f n) (simplexSubdivisionChains_naturality i.succAbove)
  change _ ≫ _ = _ ≫ _ at h
  rw [← h, ← Category.assoc, tupleGen_map]
  have hv : (StdSimplex.single (R := ℝ)) ∘ i.succAbove =
      StdSimplex.map i.succAbove ∘ StdSimplex.single := by
    funext j
    exact (StdSimplex.map_single j i.succAbove).symm
  rw [hv]

@[simp]
theorem universalSubdivision_zero :
    universalSubdivision 0 = singularGen (singularSimplexOfMap (ContinuousMap.id _)) := by
  change tupleGen StdSimplex.single ≫ tupleSubdivisionMap simplexTupleCenter 0 ≫ _ = _
  rw [tupleSubdivisionMap_zero, Category.id_comp, tupleGen_vertices_affine]

@[simp]
theorem universalSubdivisionPrism_zero : universalSubdivisionPrism 0 = 0 := by
  unfold universalSubdivisionPrism simplexSubdivisionPrism
  rw [tupleSubdivisionPrism_zero, zero_comp, comp_zero]

/-- The boundary of the universal prism includes the lower-dimensional prisms
on every oriented face. -/
theorem universalSubdivisionPrism_boundary (n : ℕ) :
    universalSubdivisionPrism (n+1) ≫
      (integralSingularChains.obj (standardSimplexSpace (n+1))).d (n+2) (n+1) =
      singularGen (singularSimplexOfMap (ContinuousMap.id _)) - universalSubdivision (n+1) -
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (universalSubdivisionPrism n ≫
          (integralSingularChains.map (standardSimplexMap i.succAbove)).f (n+1)) := by
  unfold universalSubdivisionPrism simplexSubdivisionPrism
  simp only [Category.assoc]
  rw [(simplexAffineChains (n+1)).comm, ← Category.assoc (tupleSubdivisionPrism _ _),
    tupleSubdivisionPrism_equation]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.assoc,
    tupleGen_vertices_affine]
  change _ - universalSubdivision (n+1) - _ = _
  congr 1
  rw [← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change tupleGen _ ≫ simplexSubdivisionPrism (n+1) n =
    tupleGen _ ≫ simplexSubdivisionPrism n n ≫ _
  rw [← simplexSubdivisionPrism_naturality, ← Category.assoc, tupleGen_map]
  have hv : (StdSimplex.single (R := ℝ)) ∘ i.succAbove =
      StdSimplex.map i.succAbove ∘ StdSimplex.single := by
    funext j
    exact (StdSimplex.map_single j i.succAbove).symm
  rw [hv]

end

end Kaplansky

end

end OAI
