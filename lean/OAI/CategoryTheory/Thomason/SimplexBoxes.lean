import Mathlib
import OAI.CategoryTheory.Thomason.CubicalRecognition

namespace OAI

/-! Simplex Boxes. -/

noncomputable section
universe u v w z
open Set Metric Bornology Filter
open scoped Topology BigOperators

namespace Thomason.GeometricRecognition.SimplexGeometry

def chartBody (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma chartBody_closed (n : ℕ) : IsClosed (chartBody n) := by
  have h := (isClosed_iInter fun i : Fin n =>
    isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))).inter
    (isClosed_le (show Continuous (fun x : Fin n → ℝ => ∑ i, x i) by fun_prop)
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ))))
  simpa only [chartBody,Set.ofPred_forall,Set.ofPred_and] using h

lemma chartBody_convex (n : ℕ) : Convex ℝ (chartBody n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

lemma chartBody_bounded (n : ℕ) : IsBounded (chartBody n) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin n → ℝ) 1)).isBounded.subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma strict_subset_interior_chartBody (n : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} ⊆ interior (chartBody n) := by
  have ho : IsOpen {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} :=
    by
      have h := (isOpen_iInter_of_finite fun i : Fin n => isOpen_lt (continuous_const (y := (0 : ℝ)))
        (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))).inter
        (isOpen_lt (show Continuous (fun x : Fin n → ℝ => ∑ i, x i) by fun_prop)
          (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ))))
      simpa only [Set.ofPred_forall,Set.ofPred_and] using h
  exact interior_maximal (fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩) ho

lemma chartBody_interior_nonempty (n : ℕ) : (interior (chartBody n)).Nonempty := by
  refine ⟨fun _ => 1 / ((n : ℝ)+1),strict_subset_interior_chartBody n ?_⟩
  constructor
  · intro i; positivity
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : (0 : ℝ) < n+1 := by positivity
    rw [mul_one_div,div_lt_one hn]
    linarith

lemma isOpenMap_sum (n : ℕ) [Nonempty (Fin n)] :
    IsOpenMap (fun x : Fin n → ℝ => ∑ i, x i) := by
  classical
  let f : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
  have hf : Function.Surjective f := by
    intro r
    refine ⟨Pi.single (Classical.arbitrary (Fin n)) r,?_⟩
    simp [f]
  have he : (f : (Fin n → ℝ) → ℝ) = fun x => ∑ i, x i := by
    funext x
    simp [f]
  rw [← he]
  exact f.isOpenMap hf

lemma interior_chartBody (n : ℕ) [Nonempty (Fin n)] :
    interior (chartBody n) = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  apply Set.Subset.antisymm _ (strict_subset_interior_chartBody n)
  intro x hx
  constructor
  · intro i
    have h := (isOpenMap_eval (X := fun _ : Fin n => ℝ) i).mapsTo_interior
      (s := chartBody n) (t := Set.Ici 0) (fun y hy => hy.1 i) hx
    simpa only [interior_Ici,Set.mem_Ioi] using h
  · have h := (isOpenMap_sum n).mapsTo_interior (s := chartBody n)
      (t := Set.Iic 1) (fun y hy => hy.2) hx
    simpa only [interior_Iic,Set.mem_Iio] using h

lemma mem_frontier_chartBody (n : ℕ) [Nonempty (Fin n)] (x : chartBody n) :
    x.val ∈ frontier (chartBody n) ↔ (∃ i, x.val i = 0) ∨ ∑ i, x.val i = 1 := by
  rw [frontier, (chartBody_closed n).closure_eq,Set.mem_sdiff,interior_chartBody]
  simp only [x.property,true_and,Set.mem_ofPred_eq,not_and_or,not_forall,not_lt]
  constructor
  · rintro (⟨i,hi⟩|hs)
    · exact Or.inl ⟨i,le_antisymm hi (x.property.1 i)⟩
    · exact Or.inr (le_antisymm x.property.2 hs)
  · rintro (⟨i,hi⟩|hs)
    · exact Or.inl ⟨i,hi.le⟩
    · exact Or.inr hs.ge

abbrev cubeBody (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

lemma interior_cubeBody (n : ℕ) :
    interior (cubeBody n) = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  apply Set.Subset.antisymm
  · intro x hx i
    have h := (isOpenMap_eval (X := fun _ : Fin n => ℝ) i).mapsTo_interior
      (s := cubeBody n) (t := Set.Icc 0 1) (fun y hy => ⟨hy.1 i,hy.2 i⟩) hx
    simpa only [interior_Icc,Set.mem_Ioo] using h
  · apply interior_maximal
    · exact fun x hx => ⟨fun i => (hx i).1.le,fun i => (hx i).2.le⟩
    · have h := isOpen_iInter_of_finite fun i : Fin n =>
        (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).preimage (continuous_apply i)
      convert h using 1
      ext x
      simp only [Set.mem_iInter,Set.mem_preimage,Set.mem_Ioo,Set.mem_ofPred_eq]

lemma cubeBody_interior_nonempty (n : ℕ) : (interior (cubeBody n)).Nonempty := by
  refine ⟨fun _ => (1/2 : ℝ),?_⟩
  rw [interior_cubeBody]
  intro i; norm_num

lemma mem_frontier_cubeBody (n : ℕ) (x : cubeBody n) :
    x.val ∈ frontier (cubeBody n) ↔ ∃ i, x.val i = 0 ∨ x.val i = 1 := by
  rw [frontier,isClosed_Icc.closure_eq,interior_cubeBody,Set.mem_sdiff]
  simp only [x.property,true_and,Set.mem_ofPred_eq,not_forall,not_and_or,not_lt]
  constructor
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (le_antisymm hi (x.property.1 i))⟩
    · exact ⟨i,Or.inr (le_antisymm (x.property.2 i) hi)⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl hi.le⟩
    · exact ⟨i,Or.inr hi.ge⟩

def simplexChartHomeomorph (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ chartBody n where
  toFun x := ⟨fun i => x.weights i.succ,⟨fun i => x.weights_nonneg i.succ,by
    have h := x.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith [x.weights_nonneg 0]⟩⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (1-∑i,x.val i) x.val)
    nonneg := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.property.2
      · exact x.property.1 j
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change ∑ i, Fin.cons (1-∑j,x.val j) x.val i = 1
      simp [Fin.sum_univ_succ] }
  left_inv x := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    change Fin.cons (α := fun _ => ℝ) (1-∑index : Fin n,x.weights index.succ)
      (fun index : Fin n => x.weights index.succ) i = x.weights i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have h := x.total_of_fintype
      rw [Fin.sum_univ_succ] at h
      linarith
    · simp only [Fin.cons_succ]
  right_inv x := by ext i; rfl
  continuous_toFun := (continuous_pi fun index : Fin n =>
    Convexity.StdSimplex.continuous_weights_apply ℝ index.succ).subtype_mk _
  continuous_invFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : chartBody n => 1-∑j,x.val j)
      fun_prop
    · exact (continuous_apply j).comp continuous_subtype_val

def cubeBodyHomeomorph (n : ℕ) : cubeBody n ≃ₜ (Fin n → unitInterval) where
  toFun x i := ⟨x.val i,x.property.1 i,x.property.2 i⟩
  invFun x := ⟨fun i => (x i).val,⟨fun i => (x i).property.1,fun i => (x i).property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by fun_prop

lemma exists_chart_cube (n : ℕ) : ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
    e '' chartBody n = cubeBody n ∧ e '' frontier (chartBody n) = frontier (cubeBody n) := by
  obtain ⟨e,_,he,hf⟩ := exists_homeomorph_image_eq (chartBody_convex n)
    (chartBody_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ (chartBody_bounded n))
    (convex_Icc (0 : Fin n → ℝ) 1) (cubeBody_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ
      (isCompact_Icc : IsCompact (cubeBody n)).isBounded)
  exact ⟨e,by simpa only [(chartBody_closed n).closure_eq,isClosed_Icc.closure_eq] using he,hf⟩

def chartCubeAmbient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_chart_cube n).choose

lemma chartCubeAmbient_spec (n : ℕ) :
    chartCubeAmbient n '' chartBody n = cubeBody n ∧
    chartCubeAmbient n '' frontier (chartBody n) = frontier (cubeBody n) :=
  (exists_chart_cube n).choose_spec

def simplexCubeHomeomorph (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ (Fin n → unitInterval) :=
  (simplexChartHomeomorph n).trans (((chartCubeAmbient n).image (chartBody n)).trans
    ((Homeomorph.setCongr (chartCubeAmbient_spec n).1).trans (cubeBodyHomeomorph n)))

lemma simplexCubeHomeomorph_boundary (n : ℕ) [Nonempty (Fin n)]
    (x : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (∃ i, x.weights i = 0) ↔ simplexCubeHomeomorph n x ∈ Cube.boundary (Fin n) := by
  have hc : (∃ i, x.weights i = 0) ↔
      (simplexChartHomeomorph n x).val ∈ frontier (chartBody n) := by
    rw [mem_frontier_chartBody]
    constructor
    · rintro ⟨i,hi⟩
      refine Fin.cases ?_ (fun j hj => ?_) i hi
      · intro hzero
        right
        have h := x.total_of_fintype
        rw [Fin.sum_univ_succ,hzero,zero_add] at h
        exact h
      · exact Or.inl ⟨j,hj⟩
    · rintro (⟨i,hi⟩|hs)
      · exact ⟨i.succ,hi⟩
      · refine ⟨0,?_⟩
        have h := x.total_of_fintype
        rw [Fin.sum_univ_succ] at h
        change ∑ i : Fin n, x.weights i.succ = 1 at hs
        linarith
  rw [hc]
  let y : cubeBody n := ⟨chartCubeAmbient n (simplexChartHomeomorph n x).val,by
    rw [← (chartCubeAmbient_spec n).1]
    exact ⟨_,(simplexChartHomeomorph n x).property,rfl⟩⟩
  have he : (simplexChartHomeomorph n x).val ∈ frontier (chartBody n) ↔
      y.val ∈ frontier (cubeBody n) := by
    rw [← (chartCubeAmbient_spec n).2]
    exact ((chartCubeAmbient n).injective.mem_set_image).symm
  rw [he,mem_frontier_cubeBody]
  change (∃i,y.val i=0 ∨ y.val i=1) ↔ _
  constructor
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (Subtype.ext hi)⟩
    · exact ⟨i,Or.inr (Subtype.ext hi)⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (congrArg Subtype.val hi)⟩
    · exact ⟨i,Or.inr (congrArg Subtype.val hi)⟩
end Thomason.GeometricRecognition.SimplexGeometry

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev simplexVertices (m : ℕ) : PartOrd.{u} := PartOrd.of (ULift.{u} (Fin (m+1)))
abbrev simplexPoset (m : ℕ) : PartOrd.{u} := PartOrd.of (NonemptyFiniteChains (simplexVertices.{u} m))
def simplexBoundary (m : ℕ) : Set (simplexPoset.{u} m) := {s | s.finset ≠ Finset.univ}

def simplexPolyCoordinates (m : ℕ) (x : PolyPoint (simplexVertices.{u} m)) :
    Convexity.StdSimplex ℝ (Fin (m+1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i => x.weights (ULift.up i))
  nonneg i := x.nonneg (ULift.up i)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (m+1), x.weights (ULift.up i) = 1
    calc
      ∑ i, x.weights (ULift.up i) = ∑ i : ULift.{u} (Fin (m+1)), x.weights i :=
        Equiv.sum_comp Equiv.ulift.symm x.weights
      _ = 1 := (Finsupp.sum_fintype x.weights (fun _ r => r) (fun _ => rfl)).symm.trans x.total

def simplexVertexOrder (m : ℕ) : Fin (m+1) →o simplexVertices.{u} m :=
  ⟨ULift.up,fun _ _ h => h⟩

lemma continuous_simplexPolyCoordinates (m : ℕ) : Continuous (simplexPolyCoordinates.{u} m) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  exact continuous_pi fun i => continuous_weights (ULift.up i)

def simplexPolyHomeomorph (m : ℕ) : PolyPoint (simplexVertices.{u} m) ≃ₜ Convexity.StdSimplex ℝ (Fin (m+1)) where
  toFun := simplexPolyCoordinates m
  invFun := eval (simplexVertexOrder m)
  left_inv x := by
    apply PolyPoint.ext
    ext i
    exact evalWeights_apply_image (simplexVertexOrder m) ULift.up_injective _ i.down
  right_inv x := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    exact evalWeights_apply_image (simplexVertexOrder m) ULift.up_injective _ i
  continuous_toFun := continuous_simplexPolyCoordinates m
  continuous_invFun := continuous_eval (simplexVertexOrder m)

lemma simplex_subdivide_boundary (m : ℕ) (x : PolyPoint (simplexPoset.{u} m)) :
    (∃ y : PolyPoint (simplexBoundary m), map (inclusion (simplexBoundary m))
      (preservesChains_monotone _) y = x) ↔
      ∃ i, (simplexPolyCoordinates m (subdivide x)).weights i = 0 := by
  classical
  rw [exists_of_support]
  have hne : x.weights.support.Nonempty := (supportIndex x).nonempty
  obtain ⟨s,hs,hm⟩ := flag_has_max _ x.chain hne
  have hsupport : (subdivide x).weights.support = s.finset := by
    change (barycentricLinear x.weights).support = _
    rw [barycentricLinear_support_eq _ x.nonneg,flag_union_eq_max _ s hs hm]
  constructor
  · intro h
    have hh : s.finset ≠ Finset.univ := h s hs
    have hex : ∃ i, i ∉ s.finset := by
      by_contra! h
      exact hh (Finset.eq_univ_of_forall h)
    obtain ⟨i,hi⟩ := hex
    refine ⟨i.down,?_⟩
    change (subdivide x).weights i = 0
    exact Finsupp.notMem_support_iff.mp (by simpa only [hsupport] using hi)
  · rintro ⟨i,hi⟩ t ht he
    have hi' : ULift.up i ∉ (subdivide x).weights.support := Finsupp.notMem_support_iff.mpr hi
    rw [hsupport] at hi'
    exact hi' (hm t ht (he ▸ Finset.mem_univ _))

def simplexCubicalPair (n : ℕ) : CubicalPair (simplexPoset.{u} (n+1))
    (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1))) n where
  home := subdivisionHomeomorph.trans ((simplexPolyHomeomorph (n+1)).trans
    (SimplexGeometry.simplexCubeHomeomorph (n+1)))
  boundary x := (simplex_subdivide_boundary (n+1) x).trans
    (SimplexGeometry.simplexCubeHomeomorph_boundary (n+1) _)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev orderedBoundary (m : ℕ) := orderedSimplexSubcomplex (SSet.boundary.{u} m)

lemma mem_orderedBoundary (m k : ℕ) (s : (nerve (simplexVertices.{u} m)) _⦋k⦌) :
    s ∈ (orderedBoundary m).obj _ ↔ (simplexChain s).finset ≠ Finset.univ := by
  classical
  have hmem : s ∈ (orderedBoundary m).obj _ ↔
      (SSet.stdSimplex.isoNerve m).inv.app _ s ∈ (SSet.boundary m).obj _ := by
    change (∃ x : (SSet.boundary m : SSet.{u}) _⦋k⦌,
      (SSet.stdSimplex.isoNerve m).hom.app _ x.val = s) ↔ _
    constructor
    · rintro ⟨x,rfl⟩
      simp
    · intro hs
      exact ⟨⟨_,hs⟩,by simp⟩
  rw [hmem,SSet.mem_boundary_iff_notMem_range]
  constructor
  · rintro ⟨i,hi⟩ he
    have hh : ULift.up i ∈ (simplexChain s).finset := he ▸ Finset.mem_univ _
    obtain ⟨j,hj⟩ := (mem_simplexChain s _).mp hh
    apply hi
    exact ⟨j,congrArg ULift.down hj⟩
  · intro h
    have hex : ∃ i, i ∉ (simplexChain s).finset := by
      by_contra! hh
      exact h (Finset.eq_univ_of_forall hh)
    obtain ⟨i,hi⟩ := hex
    refine ⟨i.down,?_⟩
    rintro ⟨j,hj⟩
    apply hi
    apply (mem_simplexChain s _).mpr
    exact ⟨j,ULift.ext _ _ hj⟩

lemma allowed_orderedBoundary (m : ℕ) (c : simplexPoset.{u} m) :
    (∃ s : (orderedBoundary m : SSet).N,
      simplexChain (subcomplexN (orderedBoundary m) s).simplex = c) ↔ c ∈ simplexBoundary m := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (mem_orderedBoundary m s.dim s.simplex.val).mp s.simplex.property
  · intro hc
    let t := chainSimplex c
    have ht : t.simplex ∈ (orderedBoundary m).obj _ := by
      rw [mem_orderedBoundary,simplexChain_chainSimplex]
      exact hc
    let s : (orderedBoundary m : SSet).N :=
      SSet.N.mk ⟨t.simplex,ht⟩ (((orderedBoundary m).mem_nonDegenerate_iff _).mpr t.nonDegenerate)
    exact ⟨s,simplexChain_chainSimplex c⟩

def boundaryFaceOrderIso (m : ℕ) : AllowedChains (orderedBoundary.{u} m) ≃o simplexBoundary m where
  toFun c := ⟨c.val,(allowed_orderedBoundary m c.val).mp c.property⟩
  invFun c := ⟨c.val,(allowed_orderedBoundary m c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

def sdBoundaryFacesIso (m : ℕ) : SSet.sd.obj (SSet.boundary.{u} m : SSet) ≅
    nerve (simplexBoundary.{u} m) :=
  sdSimplexSubcomplexIso (SSet.boundary m) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (orderedBoundary m)))
      (β := PartOrd.of (simplexBoundary m)) (boundaryFaceOrderIso m))

lemma sd_boundary_square (m : ℕ) :
    SSet.sd.map (SSet.boundary.{u} m).ι ≫ (sdSimplexIso m).hom =
      (sdBoundaryFacesIso m).hom ≫ nerveMap (inclusion (simplexBoundary m)).toFunctor := by
  rw [sdSimplexSubcomplexIso_naturality]
  rfl

def simplexPairProjection (m : ℕ) : nerve (simplexPoset.{u} m) ⟶ Δ[m] :=
  (sdSimplexIso m).inv ≫ lastVertex.app Δ[m]
def simplexBoundaryProjection (m : ℕ) : nerve (simplexBoundary.{u} m) ⟶ (SSet.boundary m : SSet) :=
  (sdBoundaryFacesIso m).inv ≫ lastVertex.app (SSet.boundary m : SSet)

lemma simplex_pair_square (m : ℕ) :
    nerveMap (inclusion (simplexBoundary.{u} m)).toFunctor ≫ simplexPairProjection m =
      simplexBoundaryProjection m ≫ (SSet.boundary m).ι := by
  apply (cancel_epi (sdBoundaryFacesIso m).hom).mp
  simp only [simplexPairProjection,simplexBoundaryProjection,← Category.assoc]
  rw [← sd_boundary_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact lastVertex.naturality (SSet.boundary m).ι

lemma simplexPairProjection_local (m : ℕ) : Local (simplexPairProjection.{u} m) :=
  local_comp (local_iso _) (lastVertex_local _)
lemma simplexBoundaryProjection_local (m : ℕ) : Local (simplexBoundaryProjection.{u} m) :=
  local_comp (local_iso _) (lastVertex_local _)

instance simplexBoundaryInclusion_mono (m : ℕ) :
    Mono (nerveMap (inclusion (simplexBoundary.{u} m)).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

theorem weak_simplex_injective (n : ℕ) {K L : SSet.{u}} [SSet.KanComplex K]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a b : (Δ[n+1] : SSet.{u}) ⟶ K)
    (ha : (SSet.boundary (n+1)).ι ≫ a = SSet.const x)
    (hb : (SSet.boundary (n+1)).ι ≫ b = SSet.const x)
    (H : BasedHomotopy (SSet.boundary (n+1)).ι (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (SSet.boundary (n+1)).ι (SSet.const x) a b := by
  let f := simplexPairProjection.{u} (n+1)
  let g := simplexBoundaryProjection.{u} (n+1)
  let j := nerveMap (inclusion (simplexBoundary.{u} (n+1))).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const x := by
    rw [← Category.assoc,simplex_pair_square,Category.assoc,ha,SSet.comp_const]
  have hb' : j ≫ f ≫ b = SSet.const x := by
    rw [← Category.assoc,simplex_pair_square,Category.assoc,hb,SSet.comp_const]
  have H' : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ a) ≫ r) ((f ≫ b) ≫ r) := by
    simpa only [SSet.comp_const,Category.assoc] using based_homotopy_pre
      _ j f g (simplex_pair_square _) _ H
  obtain ⟨G,hG⟩ := weak_cubical_injective (simplexPoset (n+1))
    (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1)))
    Subtype.val_injective n (simplexCubicalPair n) r hr x (f ≫ a) (f ≫ b) ha' hb' H'
  exact pair_local_injective_plain _ j f g (simplex_pair_square _)
    (simplexPairProjection_local _) (simplexBoundaryProjection_local _) _ a b ha hb G
    (by simpa only [SSet.comp_const] using hG)

theorem weak_simplex_surjective (n : ℕ) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a : (Δ[n+1] : SSet.{u}) ⟶ L)
    (ha : (SSet.boundary (n+1)).ι ≫ a = SSet.const (r.app _ x)) :
    ∃ b : (Δ[n+1] : SSet.{u}) ⟶ K, (SSet.boundary (n+1)).ι ≫ b = SSet.const x ∧
      BasedHomotopy (SSet.boundary (n+1)).ι (SSet.const (r.app _ x)) (b ≫ r) a := by
  let f := simplexPairProjection.{u} (n+1)
  let g := simplexBoundaryProjection.{u} (n+1)
  let j := nerveMap (inclusion (simplexBoundary.{u} (n+1))).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const (r.app _ x) := by
    rw [← Category.assoc,simplex_pair_square,Category.assoc,ha,SSet.comp_const]
  obtain ⟨b',hb',H'⟩ := weak_cubical_surjective (simplexPoset (n+1))
    (simplexBoundary (n+1)) n (simplexCubicalPair n) r hr x (f ≫ a) ha'
  obtain ⟨b,G,hb,hG⟩ := pair_local_surjective_plain (SSet.boundary (n+1)).ι j f g
    (simplex_pair_square _) (simplexPairProjection_local _) (simplexBoundaryProjection_local _)
    (SSet.const x) b' (by simpa only [SSet.comp_const] using hb')
  have HG : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ b) ≫ r) (b' ≫ r) := by
    simpa only [SSet.comp_const,SSet.const_comp] using
      based_homotopy_post j (SSet.const x) ⟨G,by simpa only [SSet.comp_const] using hG⟩ r
  obtain ⟨F,hF⟩ := based_homotopy_trans j (SSet.const (r.app _ x)) HG H'
  let F' : SSet.Homotopy (f ≫ (b ≫ r)) (f ≫ a) := CoherentGluing.toHomotopy F.h
    (by simpa only [Category.assoc] using F.h₀) F.h₁
  refine ⟨b,hb,pair_local_injective_plain _ j f g (simplex_pair_square _)
    (simplexPairProjection_local _) (simplexBoundaryProjection_local _)
    (SSet.const (r.app _ x)) (b ≫ r) a ?_ ha F' ?_⟩
  · rw [← Category.assoc,hb,SSet.const_comp]
  · simpa only [F', CoherentGluing.toHomotopy, SSet.comp_const] using hF
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

def boxBoundary (I : Type u) : (nerve (Finset I)).Subcomplex where
  obj k := {s | ∃ i : I, (∀ j, i ∉ s.obj j) ∨ (∀ j, i ∈ s.obj j)}
  map θ := by
    rintro s ⟨i,hi⟩
    exact ⟨i,hi.imp (fun h j => h _) (fun h j => h _)⟩

lemma mem_boxBoundary {I : Type u} [Fintype I] (k : ℕ)
    (s : (nerve (Finset I)) _⦋k⦌) :
    s ∈ (boxBoundary I).obj _ ↔ simplexChain s ∈ Cubical.boundaryFaces I := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,hi.imp ?_ ?_⟩
    · intro h v hv
      obtain ⟨j,rfl⟩ := (mem_simplexChain s v).mp hv
      exact h j
    · intro h v hv
      obtain ⟨j,rfl⟩ := (mem_simplexChain s v).mp hv
      exact h j
  · rintro ⟨i,hi⟩
    exact ⟨i,hi.imp (fun h j => h _ ((mem_simplexChain s _).mpr ⟨j,rfl⟩))
      (fun h j => h _ ((mem_simplexChain s _).mpr ⟨j,rfl⟩))⟩

lemma allowed_boxBoundary {I : Type u} [Fintype I] (c : NonemptyFiniteChains (Finset I)) :
    (∃ s : (boxBoundary I : SSet).N,
      simplexChain (subcomplexN (boxBoundary I) s).simplex = c) ↔ c ∈ Cubical.boundaryFaces I := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (mem_boxBoundary s.dim s.simplex.val).mp s.simplex.property
  · intro hc
    let t := chainSimplex c
    have ht : t.simplex ∈ (boxBoundary I).obj _ := by
      rw [mem_boxBoundary,simplexChain_chainSimplex]
      exact hc
    let s : (boxBoundary I : SSet).N :=
      SSet.N.mk ⟨t.simplex,ht⟩ (((boxBoundary I).mem_nonDegenerate_iff _).mpr t.nonDegenerate)
    exact ⟨s,simplexChain_chainSimplex c⟩

def boxBoundaryFaceIso (I : Type u) [Fintype I] :
    AllowedChains (boxBoundary I) ≃o Cubical.boundaryFaces I where
  toFun c := ⟨c.val,(allowed_boxBoundary c.val).mp c.property⟩
  invFun c := ⟨c.val,(allowed_boxBoundary c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def sdBoxBoundaryIso (I : Type u) [Fintype I] :
    SSet.sd.obj (boxBoundary I : SSet) ≅ nerve (Cubical.boundaryFaces I) :=
  sdSubcomplexIso (boxBoundary I) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (boxBoundary I)))
      (β := PartOrd.of (Cubical.boundaryFaces I)) (boxBoundaryFaceIso I))

lemma sd_box_boundary_square (I : Type u) [Fintype I] :
    SSet.sd.map (boxBoundary I).ι ≫ (sdNerveIso (E := Finset I)).hom =
      (sdBoxBoundaryIso I).hom ≫ nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor :=
  sdSubcomplexMap_naturality (boxBoundary I)

def boxPairProjection (I : Type u) : nerve (NonemptyFiniteChains (Finset I)) ⟶ nerve (Finset I) :=
  (sdNerveIso (E := Finset I)).inv ≫ lastVertex.app _
def boxBoundaryProjection (I : Type u) [Fintype I] :
    nerve (Cubical.boundaryFaces I) ⟶ (boxBoundary I : SSet) :=
  (sdBoxBoundaryIso I).inv ≫ lastVertex.app _

lemma box_pair_square (I : Type u) [Fintype I] :
    nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor ≫ boxPairProjection I =
      boxBoundaryProjection I ≫ (boxBoundary I).ι := by
  apply (cancel_epi (sdBoxBoundaryIso I).hom).mp
  simp only [boxPairProjection,boxBoundaryProjection,← Category.assoc]
  rw [← sd_box_boundary_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact lastVertex.naturality (boxBoundary I).ι

lemma boxPairProjection_local (I : Type u) : Local (boxPairProjection I) :=
  local_comp (local_iso _) (lastVertex_local _)
lemma boxBoundaryProjection_local (I : Type u) [Fintype I] : Local (boxBoundaryProjection I) :=
  local_comp (local_iso _) (lastVertex_local _)

instance boxBoundaryInclusion_mono (I : Type u) [Fintype I] :
    Mono (nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective

def finiteBoxPair (I : Type u) [Fintype I] [LinearOrder I] (n : ℕ) (e : I ≃ Fin (n+1)) :
    CubicalPair (PartOrd.of (NonemptyFiniteChains (Finset I)))
      (PartOrd.of (Cubical.boundaryFaces I)) (inclusion (Cubical.boundaryFaces I)) n where
  home := Cubical.pairCubeHomeomorph.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
  boundary := by
    intro a
    have he : (Cubical.pairCubeHomeomorph (I := I)) a ∈ Cube.boundary I ↔
        (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
          (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1)) := by
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨e j,by simpa using hj⟩
      · rintro ⟨j,hj⟩
        obtain ⟨i,rfl⟩ := e.surjective j
        exact ⟨i,by simpa only [Homeomorph.piCongrLeft_apply_apply] using hj⟩
    change _ ↔ (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
      (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1))
    rw [← he]
    constructor
    · rintro ⟨b,rfl⟩
      exact (Cubical.boundaryHomeomorph b).property
    · intro ha
      obtain ⟨b,hb⟩ := Cubical.boundaryHomeomorph.surjective ⟨_,ha⟩
      exact ⟨b,Cubical.pairCubeHomeomorph.injective (congrArg Subtype.val hb)⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

private def bit (I : Type u) : Finset (Option I) →o Fin 2 := by
  classical
  refine ⟨fun s => if none ∈ s then 1 else 0,?_⟩
  intro s t h
  dsimp only
  split_ifs with hs ht ht <;> try omega
  exact False.elim (ht (h hs))

private def pack (I : Type u) (s : Finset I) (t : Fin 2) : Finset (Option I) :=
  if t = 0 then s.map Function.Embedding.some else Finset.insertNone s

private lemma some_mem_pack {I : Type u} (s : Finset I) (t : Fin 2) (i : I) :
    some i ∈ pack I s t ↔ i ∈ s := by
  classical
  simp only [pack]
  split_ifs <;> simp

private lemma none_mem_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    none ∈ pack I s t ↔ t = 1 := by
  classical
  fin_cases t <;> simp [pack]

private def packOrder (I : Type u) : Finset I × Fin 2 →o Finset (Option I) where
  toFun st := pack I st.1 st.2
  monotone' := by
    intro s t h i hi
    cases i with
    | none =>
      rw [none_mem_pack] at hi ⊢
      have hh := h.2
      rw [hi] at hh
      omega
    | some i =>
      rw [some_mem_pack] at hi ⊢
      exact h.1 hi

private lemma eraseNone_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    Finset.eraseNone (pack I s t) = s := by
  ext i
  simp only [Finset.mem_eraseNone,some_mem_pack]

private lemma bit_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    bit I (pack I s t) = t := by
  classical
  change (if none ∈ pack I s t then (1 : Fin 2) else 0) = t
  fin_cases t <;> simp [none_mem_pack]

private lemma pack_eraseNone_bit {I : Type u} (s : Finset (Option I)) :
    pack I (Finset.eraseNone s) (bit I s) = s := by
  classical
  ext i
  cases i with
  | none =>
    rw [none_mem_pack]
    change (if none ∈ s then (1 : Fin 2) else 0) = 1 ↔ none ∈ s
    simp
  | some i => simp only [some_mem_pack,Finset.mem_eraseNone]

private def simplexOrder {P : Type u} [PartialOrder P] {n : ℕ}
    (s : (nerve P) _⦋n⦌) : Fin (n+1) →o P :=
  ⟨s.obj, fun _ _ h => leOfHom (s.map (homOfLE h))⟩

def boxToPrism (I : Type u) : nerve (Finset (Option I)) ⟶ nerve (Finset I) ⊗ Δ[1] where
  app n := TypeCat.ofHom fun s =>
    ⟨s ⋙ Finset.eraseNone.toFunctor, SSet.stdSimplex.objMk ((bit I).comp (simplexOrder s))⟩
  naturality n m θ := by
    ext s
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

def prismToBox (I : Type u) : nerve (Finset I) ⊗ Δ[1] ⟶ nerve (Finset (Option I)) where
  app n := TypeCat.ofHom fun s =>
    ((packOrder I).comp ((simplexOrder s.1).prod (SSet.stdSimplex.asOrderHom s.2))).toFunctor
  naturality n m θ := by
    ext s j
    rfl

def boxPrismIso (I : Type u) : nerve (Finset (Option I)) ≅ nerve (Finset I) ⊗ Δ[1] where
  hom := boxToPrism I
  inv := prismToBox I
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (h_obj := fun j => pack_eraseNone_bit (s.obj j))
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (h_obj := fun j =>
        eraseNone_pack (s.1.obj j) (SSet.stdSimplex.asOrderHom s.2 j))
    · apply SSet.stdSimplex.ext
      intro j
      exact bit_pack (s.1.obj j) (SSet.stdSimplex.asOrderHom s.2 j)

lemma prismToBox_side_mem (I : Type u) (n : ℕ)
    (s : (boxBoundary I : SSet) _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (prismToBox I).app _ (s.val,t) ∈ (boxBoundary (Option I)).obj _ := by
  obtain ⟨i,hi⟩ := s.property
  refine ⟨some i,hi.imp ?_ ?_⟩
  · intro h j
    change some i ∉ pack I (s.val.obj j) (SSet.stdSimplex.asOrderHom t j)
    simpa only [some_mem_pack] using h j
  · intro h j
    change some i ∈ pack I (s.val.obj j) (SSet.stdSimplex.asOrderHom t j)
    simpa only [some_mem_pack] using h j

lemma prismToBox_end_mem (I : Type u) (n : ℕ)
    (s : (nerve (Finset I)) _⦋n⦌) (t : Fin 2) :
    (prismToBox I).app _ (s,SSet.stdSimplex.const _ t _) ∈ (boxBoundary (Option I)).obj _ := by
  refine ⟨none,?_⟩
  fin_cases t
  · left
    intro j
    change none ∉ pack I (s.obj j) 0
    simp only [none_mem_pack]
    decide
  · right
    intro j
    change none ∈ pack I (s.obj j) 1
    exact (none_mem_pack _ _).mpr rfl

def prismBoxSide (I : Type u) : (boxBoundary I : SSet) ⊗ Δ[1] ⟶ (boxBoundary (Option I) : SSet) where
  app n := TypeCat.ofHom fun st => ⟨(prismToBox I).app n (st.1.val,st.2),
    prismToBox_side_mem I _ st.1 st.2⟩
  naturality _ _ _ := by ext; rfl

def prismBoxEnd (I : Type u) (t : Fin 2) : nerve (Finset I) ⟶ (boxBoundary (Option I) : SSet) where
  app n := TypeCat.ofHom fun s => ⟨(prismToBox I).app n (s,SSet.stdSimplex.const _ t _),
    prismToBox_end_mem I _ s t⟩
  naturality _ _ _ := by ext; rfl

lemma prismBoxSide_comp (I : Type u) :
    prismBoxSide I ≫ (boxBoundary (Option I)).ι =
      (boxBoundary I).ι ▷ Δ[1] ≫ prismToBox I := rfl
lemma prismBoxEnd_zero_comp (I : Type u) :
    prismBoxEnd I 0 ≫ (boxBoundary (Option I)).ι = SSet.ι₀ ≫ prismToBox I := rfl
lemma prismBoxEnd_one_comp (I : Type u) :
    prismBoxEnd I 1 ≫ (boxBoundary (Option I)).ι = SSet.ι₁ ≫ prismToBox I := rfl

lemma boxPrism_boundary_const (I : Type u) {K : SSet.{u}} (x : K _⦋0⦌)
    (F : nerve (Finset I) ⊗ Δ[1] ⟶ K)
    (hi : (boxBoundary I).ι ▷ Δ[1] ≫ F = SSet.const x)
    (h₀ : SSet.ι₀ ≫ F = SSet.const x) (h₁ : SSet.ι₁ ≫ F = SSet.const x) :
    (boxBoundary (Option I)).ι ≫ boxToPrism I ≫ F = SSet.const x := by
  classical
  ext n s
  obtain ⟨i,hi'⟩ := s.property
  let q := (boxToPrism I).app _ s.val
  change F.app _ q = _
  cases i with
  | some i =>
    have hq : q.1 ∈ (boxBoundary I).obj _ := by
      refine ⟨i,hi'.imp ?_ ?_⟩
      · intro h j
        change i ∉ Finset.eraseNone (s.val.obj j)
        simpa only [Finset.mem_eraseNone] using h j
      · intro h j
        change i ∈ Finset.eraseNone (s.val.obj j)
        simpa only [Finset.mem_eraseNone] using h j
    exact congrArg (fun f => f.app _ (⟨q.1,hq⟩,q.2)) hi
  | none =>
    rcases hi' with h | h
    · have he : q = SSet.ι₀.app _ q.1 := by
        apply Prod.ext
        · rfl
        apply SSet.stdSimplex.ext
        intro j
        change (if none ∈ s.val.obj j then (1 : Fin 2) else 0) = 0
        exact ite_eq_right (h j)
      rw [he]
      exact congrArg (fun f => f.app _ q.1) h₀
    · have he : q = SSet.ι₁.app _ q.1 := by
        apply Prod.ext
        · rfl
        apply SSet.stdSimplex.ext
        intro j
        change (if none ∈ s.val.obj j then (1 : Fin 2) else 0) = 1
        exact ite_eq_left (h j)
      rw [he]
      exact congrArg (fun f => f.app _ q.1) h₁
end Thomason.GeometricRecognition

end

end OAI
