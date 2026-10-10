import OAI.CategoryTheory.Thomason.Chains.FiniteChainMesh
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.PosetSubcomplexHomotopy

namespace OAI

section

/-! # Barycentric subdivision maps for finite poset realizations

The affine combination of a chain of nonempty faces is supported in its
greatest face. It therefore gives a continuous map to the original
nerve realization, with the expected affine-coordinate compatibility.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder

noncomputable section

variable (P : Type) [PartialOrder P] [Fintype P]

local instance : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
local instance : Fintype (NonemptyFiniteChains P) := Fintype.ofFinite _

def chainPoint (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) : StdSimplex ℝ P :=
  (StdSimplex.map chainDistribution
    (PosetGeometry.coordinates (NonemptyFiniteChains P) z)).sConvexComb

theorem chainPoint_weight
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) (i : P) :
    (chainPoint P z).weights i =
      ∑ A : NonemptyFiniteChains P,
        (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A *
          (chainDistribution A).weights i := by
  classical
  unfold chainPoint
  rw [StdSimplex.weights_sConvexComb]
  change ((PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights.mapDomain
    chainDistribution).sum (fun A r => r • A.weights) i = _
  rw [Finsupp.sum_mapDomain_index (h := fun (A : StdSimplex ℝ P) (r : ℝ) => r • A.weights)
    (fun _ => zero_smul ℝ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum_apply]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

theorem chainPoint_support
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) (i : P)
    (hi : (chainPoint P z).weights i ≠ 0) :
    ∃ A : NonemptyFiniteChains P,
      (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A ≠ 0 ∧ i ∈ A.finset := by
  classical
  by_contra hn
  push Not at hn
  apply hi
  rw [chainPoint_weight]
  apply Finset.sum_eq_zero
  intro A _
  by_cases hA : (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A = 0
  · rw [hA, zero_mul]
  · rw [chainDistribution_weight, ite_eq_right (hn A hA), mul_zero]

theorem chainPoint_chainSupported
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    PosetGeometry.ChainSupported (chainPoint P z) := by
  intro x hx y hy
  obtain ⟨A, hA, hxA⟩ := chainPoint_support P z x (Finsupp.mem_support_iff.mp hx)
  obtain ⟨B, hB, hyB⟩ := chainPoint_support P z y (Finsupp.mem_support_iff.mp hy)
  have hc := PosetGeometry.coordinates_chainSupported z A
    (Finsupp.mem_support_iff.mpr hA) B (Finsupp.mem_support_iff.mpr hB)
  rcases hc with hAB | hBA
  · exact B.comparable ⟨x, hAB hxA⟩ ⟨y, hyB⟩
  · exact A.comparable ⟨x, hxA⟩ ⟨y, hBA hyB⟩

def chainPointMap :
    C(SSet.toTop.obj (nerve (NonemptyFiniteChains P)), StdSimplex ℝ P) where
  toFun := chainPoint P
  continuous_toFun := by
    classical
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ P).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_def, chainPoint_weight]
    apply continuous_finsetSum
    intro A _
    exact ((StdSimplex.continuous_weights_apply ℝ A).comp
      (PosetGeometry.coordinates (NonemptyFiniteChains P)).continuous).mul continuous_const

def chainRealizationMap :
    C(SSet.toTop.obj (nerve (NonemptyFiniteChains P)), SSet.toTop.obj (nerve P)) :=
  ⟨fun z => (PosetGeometry.coordinatesHomeomorph P).symm
      ⟨chainPoint P z, (PosetGeometry.mem_range_coordinates_iff _).mpr
        (chainPoint_chainSupported P z)⟩,
    (PosetGeometry.coordinatesHomeomorph P).symm.continuous.comp
      ((chainPointMap P).continuous.subtype_mk _)⟩

theorem coordinates_chainRealizationMap
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    PosetGeometry.coordinates P (chainRealizationMap P z) = chainPoint P z :=
  congrArg Subtype.val ((PosetGeometry.coordinatesHomeomorph P).apply_symm_apply _)

theorem affineRealization_chainRealizationMap {d : ℕ} (x : P → Fin d → ℝ)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    affineRealization x (chainRealizationMap P z) =
      affineRealization (chainAverage x) z := by
  classical
  funext j
  change finiteAffineValue (fun i => x i j)
    (PosetGeometry.coordinates P (chainRealizationMap P z)) = _
  rw [coordinates_chainRealizationMap]
  unfold finiteAffineValue
  simp_rw [chainPoint_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  change (∑ i, _ * _ * x i j) =
    (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A *
      finiteAffineValue (fun i => x i j) (chainDistribution A)
  simp only [finiteAffineValue, Finset.mul_sum, mul_assoc]

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The chain-barycenter map is a weak equivalence

Its positive support and that of the greatest-vertex map belong to the
same chain. Straight interpolation therefore stays in the original
finite-poset realization. The greatest map is last vertex under
the canonical subdivision isomorphism.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

variable (P : Type) [PartialOrder P] [Fintype P]

local instance : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
local instance : Fintype (NonemptyFiniteChains P) := Fintype.ofFinite _

def greatestRealizationMap :
    C(SSet.toTop.obj (nerve (NonemptyFiniteChains P)), SSet.toTop.obj (nerve P)) :=
  (SSet.toTop.map (nerveMap (ChainLabelApproximation.greatestHom (P := P)).monotone.functor)).hom

omit [Fintype P] in
theorem greatestRealizationMap_support
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) (x : P)
    (hx : (PosetGeometry.coordinates P (greatestRealizationMap P z)).weights x ≠ 0) :
    ∃ A : NonemptyFiniteChains P,
      (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A ≠ 0 ∧ x ∈ A.finset := by
  classical
  have he := PosetGeometry.coordinates_nerveMap
    (ChainLabelApproximation.greatestHom (P := P)) z
  change PosetGeometry.coordinates P (greatestRealizationMap P z) = _ at he
  rw [he] at hx
  have hs : x ∈ ((PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights.mapDomain
      (ChainLabelApproximation.greatestHom (P := P))).support :=
    Finsupp.mem_support_iff.mpr hx
  rw [Finsupp.support_mapDomain_of_nonneg
    (PosetGeometry.coordinates (NonemptyFiniteChains P) z).nonneg] at hs
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨A, Finsupp.mem_support_iff.mp hA, ChainLabelApproximation.greatest_mem A⟩

theorem chainRealizationMap_compatible
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    PosetGeometry.CompatibleSupport
      (PosetGeometry.coordinates P (chainRealizationMap P z))
      (PosetGeometry.coordinates P (greatestRealizationMap P z)) := by
  intro x hx y hy
  have support (v : P)
      (hv : (PosetGeometry.coordinates P (chainRealizationMap P z)).weights v ≠ 0 ∨
        (PosetGeometry.coordinates P (greatestRealizationMap P z)).weights v ≠ 0) :
      ∃ A : NonemptyFiniteChains P,
        (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights A ≠ 0 ∧ v ∈ A.finset := by
    rcases hv with hv | hv
    · apply chainPoint_support P z v
      rwa [coordinates_chainRealizationMap] at hv
    · exact greatestRealizationMap_support P z v hv
  obtain ⟨A, hA, hxA⟩ := support x hx
  obtain ⟨B, hB, hyB⟩ := support y hy
  rcases PosetGeometry.coordinates_chainSupported z A (Finsupp.mem_support_iff.mpr hA)
      B (Finsupp.mem_support_iff.mpr hB) with hAB | hBA
  · exact B.comparable ⟨x, hAB hxA⟩ ⟨y, hyB⟩
  · exact A.comparable ⟨x, hxA⟩ ⟨y, hBA hyB⟩

def chainRealizationMapHomotopy :
    (chainRealizationMap P).Homotopy (greatestRealizationMap P) :=
  PosetGeometry.commonChainHomotopy _ _ (chainRealizationMap_compatible P)

theorem chainRealizationMap_weak : IsWeakHomotopyEquivalence (chainRealizationMap P) := by
  apply (PosetGeometry.compatible_support_weak_iff (chainRealizationMap P)
    (greatestRealizationMap P) (chainRealizationMap_compatible P)).mpr
  exact ChainLabelApproximation.greatest_nerveMap_weak P

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Simplex representatives inside a specified finite chain

An entire barycentrically subdivided simplex maps into its greatest
original face, including every boundary point. The representative below
uses that whole face, allowing all vertex-star labels to be retained.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

def finiteChainSimplex {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    Fin ((ChainOrdinal.choose C).dim+1) ⥤ P :=
  ({ toFun i := ((ChainOrdinal.choose C).enum i).val
     monotone' := fun _ _ h => (ChainOrdinal.choose C).enum.monotone h } :
      Fin ((ChainOrdinal.choose C).dim+1) →o P).monotone.functor

theorem finiteChainSimplex_range {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    Set.range (finiteChainSimplex C).obj = (C.finset : Set P) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((ChainOrdinal.choose C).enum i).property
  · intro hx
    obtain ⟨i, hi⟩ := (ChainOrdinal.choose C).enum.surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem exists_coordinates_on_chain {P : Type} [PartialOrder P]
    (C : NonemptyFiniteChains P) (p : StdSimplex ℝ P)
    (hp : p.weights.support ⊆ C.finset) :
    ∃ q : StdSimplex ℝ (Fin ((ChainOrdinal.choose C).dim+1)),
      StdSimplex.map (finiteChainSimplex C).obj q = p := by
  classical
  let e := (finiteChainSimplex C).obj
  have he : Function.Injective e := fun i j h =>
    (ChainOrdinal.choose C).enum.injective (Subtype.ext h)
  let q := StdSimplex.map (Function.invFun e) p
  refine ⟨q, ?_⟩
  apply StdSimplex.ext
  change (p.weights.mapDomain (Function.invFun e)).mapDomain e = p.weights
  rw [← Finsupp.mapDomain_comp]
  have hh : p.weights.mapDomain (e ∘ Function.invFun e) = p.weights.mapDomain id := by
    apply Finsupp.mapDomain_congr
    intro x hx
    have hmem : x ∈ Set.range e := by
      rw [finiteChainSimplex_range]
      exact hp hx
    obtain ⟨i, rfl⟩ := hmem
    change e (Function.invFun e (e i)) = e i
    rw [Function.leftInverse_invFun he]
  exact hh.trans Finsupp.mapDomain_id

theorem exists_point_on_chain {P : Type} [PartialOrder P]
    (C : NonemptyFiniteChains P) (z : SSet.toTop.obj (nerve P))
    (hz : (PosetGeometry.coordinates P z).weights.support ⊆ C.finset) :
    ∃ q : StdSimplex ℝ (Fin ((ChainOrdinal.choose C).dim+1)),
      z = RealizationPrism.simplexPoint (nerve P) (finiteChainSimplex C) q := by
  obtain ⟨q, hq⟩ := exists_coordinates_on_chain C (PosetGeometry.coordinates P z) hz
  refine ⟨q, PosetGeometry.coordinates_injective P ?_⟩
  exact hq.symm.trans (PosetGeometry.coordinates_simplexPoint P (finiteChainSimplex C) q).symm

theorem chainPoint_simplex_support {P : Type} [PartialOrder P] [Fintype P]
    {m : ℕ} (s : Fin (m+1) ⥤ NonemptyFiniteChains P)
    (p : StdSimplex ℝ (Fin (m+1))) :
    (chainPoint P (RealizationPrism.simplexPoint (nerve (NonemptyFiniteChains P)) s p)).weights.support ⊆
      (s.obj (Fin.last m)).finset := by
  classical
  intro x hx
  obtain ⟨A, hA, hxA⟩ := chainPoint_support P _ x (Finsupp.mem_support_iff.mp hx)
  have he := PosetGeometry.coordinates_simplexPoint (NonemptyFiniteChains P) s p
  have hmem : A ∈ (p.weights.mapDomain s.obj).support := by
    rw [← StdSimplex.weights_map, ← he]
    exact Finsupp.mem_support_iff.mpr hA
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg] at hmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
  exact leOfHom (s.map (homOfLE (Fin.le_last i))) hxA

theorem chainRealizationMap_simplex_representation {P : Type} [PartialOrder P] [Fintype P]
    {m : ℕ} (s : Fin (m+1) ⥤ NonemptyFiniteChains P)
    (p : StdSimplex ℝ (Fin (m+1))) :
    ∃ q : StdSimplex ℝ (Fin ((ChainOrdinal.choose (s.obj (Fin.last m))).dim+1)),
      chainRealizationMap P
          (RealizationPrism.simplexPoint (nerve (NonemptyFiniteChains P)) s p) =
        RealizationPrism.simplexPoint (nerve P) (finiteChainSimplex (s.obj (Fin.last m))) q := by
  apply exists_point_on_chain
  rw [coordinates_chainRealizationMap]
  exact chainPoint_simplex_support s p

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Nondegenerate faces of a poset nerve are finite chains

The identification uses the vertex image of each nondegenerate
simplex. Its last-vertex comparison agrees with the established
subdivision comparison, including the original target map.
-/

namespace Thomason.Construction.NerveFaceChains

open CategoryTheory PartialOrder Opposite
open SubdivisionBarycentric ChainLabelApproximation
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

def chainOfFace (x : (nerve P).N) : NonemptyFiniteChains P where
  finset := by classical exact Finset.univ.image x.simplex.obj
  nonempty := by classical exact Finset.univ_nonempty.image x.simplex.obj
  comparable := by
    classical
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact (le_total i j).imp (fun h => x.simplex.monotone h)
      (fun h => x.simplex.monotone h)

@[simp]
theorem mem_chainOfFace (x : (nerve P).N) (p : P) :
    p ∈ (chainOfFace x).finset ↔ ∃ i, x.simplex.obj i = p := by
  classical
  simp [chainOfFace]

theorem chainOfFace_le_iff (x y : (nerve P).N) :
    chainOfFace x ≤ chainOfFace y ↔ x ≤ y := by
  classical
  constructor
  · intro h
    have hy := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono y.simplex).mp
      y.nonDegenerate
    have hx := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x.simplex).mp
      x.nonDegenerate
    have hr (i : Fin (x.dim+1)) : x.simplex.obj i ∈ Set.range y.simplex.obj := by
      exact (mem_chainOfFace y _).mp (h ((mem_chainOfFace x _).mpr ⟨i, rfl⟩))
    let g : Fin (x.dim+1) → Fin (y.dim+1) :=
      fun i => Function.invFun y.simplex.obj (x.simplex.obj i)
    have hg (i) : y.simplex.obj (g i) = x.simplex.obj i :=
      Function.invFun_eq (hr i)
    let u : SimplexCategory.mk x.dim ⟶ SimplexCategory.mk y.dim :=
      SimplexCategory.Hom.mk ⟨g, fun i j hij =>
        hy.le_iff_le.mp (by rw [hg, hg]; exact x.simplex.monotone hij)⟩
    have hu : Mono u := by
      apply SimplexCategory.mono_iff_injective.mpr
      intro i j hij
      apply hx.injective
      rw [← hg i, ← hg j]
      exact congrArg y.simplex.obj hij
    apply SSet.N.le_iff_exists_mono.mpr
    refine ⟨u, hu, ?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact hg i
  · intro h p hp
    obtain ⟨u, _, hu⟩ := SSet.N.le_iff_exists_mono.mp h
    obtain ⟨i, rfl⟩ := (mem_chainOfFace x p).mp hp
    apply (mem_chainOfFace y _).mpr
    exact ⟨u.toOrderHom i, congrArg (fun s => s.obj i) hu⟩

def faceOfChain (C : NonemptyFiniteChains P) : (nerve P).N :=
  SSet.N.mk (finiteChainSimplex C)
    ((PartialOrder.mem_nerve_nonDegenerate_iff_injective _).mpr
      (fun _i _j h => (ChainOrdinal.choose C).enum.injective (Subtype.ext h)))

@[simp]
theorem chainOfFace_faceOfChain (C : NonemptyFiniteChains P) :
    chainOfFace (faceOfChain C) = C := by
  apply NonemptyFiniteChains.ext
  ext p
  rw [mem_chainOfFace]
  change (∃ i, (finiteChainSimplex C).obj i = p) ↔ p ∈ C.finset
  exact Set.ext_iff.mp (finiteChainSimplex_range C) p

def orderIso (P : Type) [PartialOrder P] : (nerve P).N ≃o NonemptyFiniteChains P where
  toEquiv := Equiv.ofBijective chainOfFace ⟨fun x y h =>
    le_antisymm ((chainOfFace_le_iff x y).mp h.le)
      ((chainOfFace_le_iff y x).mp h.ge), fun C => ⟨faceOfChain C, chainOfFace_faceOfChain C⟩⟩
  map_rel_iff' := chainOfFace_le_iff _ _

theorem greatest_chainOfFace (x : (nerve P).N) :
    greatest (chainOfFace x) = x.simplex.obj (Fin.last x.dim) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := (mem_chainOfFace x _).mp (greatest_mem (chainOfFace x))
    rw [← hi]
    exact x.simplex.monotone (Fin.le_last i)
  · exact le_greatest (chainOfFace x) _ ((mem_chainOfFace x _).mpr ⟨_, rfl⟩)

/-- The face-poset comparison reads exactly the greatest original vertex. -/
theorem lastVertex_eq :
    NonsingularLastVertex.map (nerve P) =
      nerveMap (orderIso P).toOrderEmbedding.toOrderHom.monotone.functor ≫
        nerveMap (greatestHom (P := P)).monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change (s.obj (Fin.last d.unop.len)).simplex.obj
      ((NonsingularLastVertex.ordinal s).toOrderHom i) = greatest (chainOfFace (s.obj i))
  rw [greatest_chainOfFace]
  exact congrArg (fun t => t.obj (Fin.last (s.obj i).dim))
    (SSet.N.map_monoOfLE (s.monotone (Fin.le_last i)))

/-- The subdivision has this face-poset as its nerve. -/
def nerveIso (P : Type) [PartialOrder P] :
    nerve (nerve P).N ≅ nerve (NonemptyFiniteChains P) where
  hom := nerveMap (orderIso P).toOrderEmbedding.toOrderHom.monotone.functor
  inv := nerveMap (orderIso P).symm.toOrderEmbedding.toOrderHom.monotone.functor
  hom_inv_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact (orderIso P).symm_apply_apply (s.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact (orderIso P).apply_symm_apply (s.obj i)

def subdivisionIso (P : Type) [PartialOrder P] [Finite P] :
    SSet.sd.obj (nerve P) ≅ nerve (nerve P).N :=
  NerveSubdivisionMap.iso P ≪≫ (nerveIso P).symm

theorem subdivisionIso_lastVertex (P : Type) [PartialOrder P] [Finite P] :
    (subdivisionIso P).hom ≫ NonsingularLastVertex.map (nerve P) =
      lastVertex.app (nerve P) := by
  rw [lastVertex_eq]
  change (NerveSubdivisionMap.iso P).hom ≫
    (nerveIso P).inv ≫ (nerveIso P).hom ≫
        nerveMap greatestHom.monotone.functor = _
  simp only [Iso.inv_hom_id_assoc]
  exact ChainLabelApproximation.subdivision_greatest_eq_lastVertex P

theorem chainOfFace_naturality {Q : Type} [PartialOrder Q]
    (f : P →o Q)
    (hf : NonsingularLastVertex.PreservesNondegenerate (nerveMap f.monotone.functor))
    (x : (nerve P).N) :
    chainOfFace (NonsingularLastVertex.faceMap (nerveMap f.monotone.functor) hf x) =
      (chainOfFace x).map f := by
  apply NonemptyFiniteChains.ext
  ext q
  rw [mem_chainOfFace, NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨x.simplex.obj j, (mem_chainOfFace x _).mpr ⟨j, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_chainOfFace x p).mp hp
    exact ⟨j, rfl⟩

@[reassoc]
theorem nerveIso_naturality {Q : Type} [PartialOrder Q]
    (f : P →o Q)
    (hf : NonsingularLastVertex.PreservesNondegenerate (nerveMap f.monotone.functor)) :
    nerveMap (NonsingularLastVertex.faceMap (nerveMap f.monotone.functor) hf).monotone.functor ≫
      (nerveIso Q).hom = (nerveIso P).hom ≫
        nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  exact chainOfFace_naturality f hf (s.obj j)

@[reassoc]
theorem subdivisionIso_naturality {Q : Type} [PartialOrder Q] [Finite P] [Finite Q]
    (f : P →o Q)
    (hf : NonsingularLastVertex.PreservesNondegenerate (nerveMap f.monotone.functor)) :
    SSet.sd.map (nerveMap f.monotone.functor) ≫ (subdivisionIso Q).hom =
      (subdivisionIso P).hom ≫ nerveMap
        (NonsingularLastVertex.faceMap (nerveMap f.monotone.functor) hf).monotone.functor := by
  apply (cancel_mono (nerveIso Q).hom).mp
  simp only [Category.assoc, subdivisionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc, nerveIso_naturality, Iso.inv_hom_id, Category.comp_id]
  exact NerveSubdivisionMap.map_naturality f

end

end Thomason.Construction.NerveFaceChains

end

end OAI
