import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.GridGlobeCylinderComparison
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.LocallyFinite

namespace OAI

section

/-! # Exact bounded atom lifts in the pushout of grid-row cylinders -/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobeCylinder

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev model := GrayChainExtension.model
abbrev Source {n k l : ℕ} (hkl : k < l) : StrictOmegaCategory.{0} :=
  GridGlobe.ImageSource (n := n) hkl model

def rowMap {n k l : ℕ} (hkl : k < l) (s : Bool) :
    model.obj (PastingGlobe.category n n k) ⟶ Source (n := n) hkl :=
  if s then pushout.inr _ _ else pushout.inl _ _

def comparison {n k l : ℕ} (hkl : k < l) :
    Source (n := n) hkl ⟶ model.obj (GridGlobe.category n k l hkl) :=
  pushout.desc (model.map (GridGlobe.row n k l hkl false))
    (model.map (GridGlobe.row n k l hkl true)) (by
      rw [← model.map_comp, ← model.map_comp]
      exact congrArg model.map (pushout.condition
        (f := GrayMapping.pastingFace true l n k hkl)
        (g := GrayMapping.pastingFace false l n k hkl)))

theorem rowMap_comparison {n k l : ℕ} (hkl : k < l) (s : Bool) :
    rowMap hkl s ≫ comparison hkl = model.map (GridGlobe.row n k l hkl s) := by
  cases s
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

def basisComparison {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Source (n := n) hkl ⟶ (rightCylinder (GridGlobeBasis.complex hkl hln)).realization :=
  comparison hkl ≫ (GridGlobeBasis.modelIso hkl hln).hom

theorem rowMap_basisComparison {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    rowMap hkl s ≫ basisComparison hkl hln =
      (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom ≫
        (RightCylinder.map (GridGlobeBasis.inclusion hkl hln s)).realization := by
  rw [basisComparison, ← Category.assoc, rowMap_comparison, GridGlobeBasis.model_row]

theorem row_image_eq {n k l : ℕ} (hkl : k < l) (hln : l < n) (s t : Bool)
    (x y : model.obj (PastingGlobe.category n n k))
    (he : (model.map (GridGlobe.row n k l hkl s)).toFun x =
      (model.map (GridGlobe.row n k l hkl t)).toFun y) :
    (rowMap hkl s).toFun x = (rowMap hkl t).toFun y := by
  cases s <;> cases t
  · exact congrArg (rowMap hkl false).toFun
      (GridGlobe.row_map_injective hkl hln.le model false he)
  · exact GridGlobe.cross_image_eq hkl hln.le model x y he
  · exact (GridGlobe.cross_image_eq hkl hln.le model y x he.symm).symm
  · exact congrArg (rowMap hkl true).toFun
      (GridGlobe.row_map_injective hkl hln.le model true he)

theorem row_image_eq_of_basisComparison {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (s t : Bool) (x y : model.obj (PastingGlobe.category n n k))
    (he : (basisComparison hkl hln).toFun ((rowMap hkl s).toFun x) =
      (basisComparison hkl hln).toFun ((rowMap hkl t).toFun y)) :
    (rowMap hkl s).toFun x = (rowMap hkl t).toFun y := by
  apply row_image_eq hkl hln s t x y
  have hs := congrArg (fun F => F.toFun x) (rowMap_comparison hkl s)
  have ht := congrArg (fun F => F.toFun y) (rowMap_comparison hkl t)
  have hh : (GridGlobeBasis.modelIso hkl hln).hom.toFun
      ((comparison hkl).toFun ((rowMap hkl s).toFun x)) =
    (GridGlobeBasis.modelIso hkl hln).hom.toFun
      ((comparison hkl).toFun ((rowMap hkl t).toFun y)) := he
  have hi (z : model.obj (GridGlobe.category n k l hkl)) :
      (GridGlobeBasis.modelIso hkl hln).inv.toFun
        ((GridGlobeBasis.modelIso hkl hln).hom.toFun z) = z :=
    congrArg (fun F => F.toFun z) (GridGlobeBasis.modelIso hkl hln).hom_inv_id
  exact hs.symm.trans ((hi _).symm.trans
    ((congrArg (GridGlobeBasis.modelIso hkl hln).inv.toFun hh).trans ((hi _).trans ht)))

abbrev atomBasis {n k l : ℕ} (hkl : k < l) (hln : l < n) :=
  GridGlobeBasis.cylinderOrderedAtomBasis hkl hln

def representativeRow {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) : Bool :=
  Classical.choose (GridGlobeBasis.cylinderAtom_in_row hkl hln a)

def representativeIndex {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) : PastingGlobeCylinderBasis.Basis n k a.1 :=
  Classical.choose (Classical.choose_spec (GridGlobeBasis.cylinderAtom_in_row hkl hln a))

theorem representative_spec {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) :
    (RightCylinder.map (GridGlobeBasis.inclusion hkl hln (representativeRow hkl hln a))).realization.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) (representativeIndex hkl hln a)) =
        (atomBasis hkl hln).atomCell a :=
  Classical.choose_spec (Classical.choose_spec (GridGlobeBasis.cylinderAtom_in_row hkl hln a))

def atomLift {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) : Source (n := n) hkl :=
  (rowMap hkl (representativeRow hkl hln a)).toFun
    ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) (representativeIndex hkl hln a)))

theorem atomLift_dimension {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) : (Source (n := n) hkl).DimensionLE a.1 (atomLift hkl hln a) :=
  (rowMap hkl _).dimensionLE ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.dimensionLE
    (PastingGlobeCylinderBasis.atom_dimension (hkl.trans hln) _))

theorem atomLift_image {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (atomBasis hkl hln).AtomIndex) :
    (basisComparison hkl hln).toFun (atomLift hkl hln a) = (atomBasis hkl hln).atomCell a := by
  have he := congrArg (fun F => F.toFun
    ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) (representativeIndex hkl hln a))))
    (rowMap_basisComparison hkl hln (representativeRow hkl hln a))
  have hi := congrArg (fun F => F.toFun
    (PastingGlobeCylinderBasis.atom (hkl.trans hln) (representativeIndex hkl hln a)))
      (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv_hom_id
  exact he.trans ((congrArg
    (RightCylinder.map (GridGlobeBasis.inclusion hkl hln (representativeRow hkl hln a))).realization.toFun hi).trans
      (representative_spec hkl hln a))

end
end Thomason.Construction.StrictOmegaCategory.GridGlobeCylinder

end

section

/-! # Barycentric splitting for the standard simplicial prism

The simplex over a prism cut duplicates one vertex. Splitting the mass at
that vertex constructs its barycentric coordinates, with an exact projection
back to the original simplex. This is the geometric input for the actual
realization of a simplicial homotopy.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- Remove a specified amount of mass from one vertex. -/
def remainder {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) (a : ℝ) :
    Fin (n+1) →₀ ℝ := x.weights - Finsupp.single j a

theorem remainder_nonneg {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (a : ℝ) (ha : a ≤ x.weights j) : 0 ≤ remainder x j a := by
  intro k
  change 0 ≤ x.weights k - Finsupp.single j a k
  by_cases h : j = k
  · subst k
    simpa using sub_nonneg.mpr ha
  · simp [Ne.symm h]

/-- Duplicate vertex `j`, assigning mass `a` to its first occurrence. -/
def splitWeights {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) (a : ℝ) :
    Fin (n+2) →₀ ℝ :=
  Finsupp.single j.castSucc a + (remainder x j a).mapDomain j.castSucc.succAbove

/-- The split weights form a genuine standard simplex. -/
def split {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ x.weights j) : StdSimplex ℝ (Fin (n+2)) where
  weights := splitWeights x j a
  nonneg := add_nonneg (Finsupp.single_nonneg.mpr ha)
    (Finsupp.mapDomain_nonneg (remainder_nonneg x j a hb))
  total := by
    unfold splitWeights remainder
    rw [Finsupp.sum_add_index' (by intro; rfl) (by intros; rfl),
      Finsupp.sum_single_index (by rfl),
      Finsupp.sum_mapDomain_index (by intro; rfl) (by intros; rfl),
      Finsupp.sum_sub_index (by intros; rfl), Finsupp.sum_single_index (by rfl), x.total]
    ring

/-- Collapsing the duplicated vertex recovers exactly the original point. -/
theorem split_projection {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ x.weights j) :
    StdSimplex.map j.predAbove (split x j a ha hb) = x := by
  apply StdSimplex.ext
  change (splitWeights x j a).mapDomain j.predAbove = x.weights
  unfold splitWeights
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Fin.predAbove_castSucc_self,
    ← Finsupp.mapDomain_comp]
  have h : j.predAbove ∘ j.castSucc.succAbove = id := by
    funext k
    exact Fin.predAbove_succAbove j k
  rw [h, Finsupp.mapDomain_id]
  unfold remainder
  abel

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The finite closed regions of the standard simplicial prism

Cumulative barycentric mass locates the simplex of the usual prism
triangulation. The regions cover the whole topological simplex times I.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

/-- Barycentric mass before the `k`th vertex. -/
def cumulative {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (k : ℕ) : ℝ :=
  ∑ i : Fin (n+1), if i.val < k then x.weights i else 0

@[simp]
theorem cumulative_zero {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) : cumulative x 0 = 0 := by
  simp [cumulative]

@[simp]
theorem cumulative_all {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) : cumulative x (n+1) = 1 := by
  simpa only [cumulative, Fin.is_lt, ite_true] using x.total_of_fintype

theorem cumulative_step {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) :
    cumulative x (j.val+1) = cumulative x j.val + x.weights j := by
  classical
  have h : ∀ i : Fin (n+1),
      (if i.val < j.val+1 then x.weights i else 0) =
      (if i.val < j.val then x.weights i else 0) + (if i = j then x.weights j else 0) := by
    intro i
    by_cases he : i = j
    · subst i; simp
    · have hn : i.val ≠ j.val := fun h => he (Fin.ext h)
      by_cases hi : i.val < j.val
      · simp [he, hi, Nat.lt_succ_of_lt hi]
      · have hi' : ¬ i.val < j.val+1 := by omega
        simp [he, hi, hi']
  simp only [cumulative, h, Finset.sum_add_distrib]
  simp

/-- Every mass threshold lies in one of the consecutive vertex intervals. -/
theorem exists_cut {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (s : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ∃ j : Fin (n+1), cumulative x j.val ≤ s ∧ s ≤ cumulative x (j.val+1) := by
  have hex : ∃ k : ℕ, k ≤ n ∧ s ≤ cumulative x (k+1) :=
    ⟨n, le_rfl, by simpa using hs₁⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  refine ⟨⟨k, by omega⟩, ?_, hk.2⟩
  by_contra! hlow
  have hpos : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    have hn : s < 0 := by simpa [he] using hlow
    exact (not_lt_of_ge hs₀) hn
  have hprev : k-1 ≤ n ∧ s ≤ cumulative x (k-1+1) := by
    constructor
    · omega
    · have he : k-1+1 = k := by omega
      rw [he]
      exact hlow.le
  have hmin := Nat.find_min' hex hprev
  change k ≤ k-1 at hmin
  omega

/-- The closed region on which the prism cut passes through vertex `j`. -/
def region {n : ℕ} (j : Fin (n+1)) : Set (StdSimplex ℝ (Fin (n+1)) × unitInterval) :=
  {p | cumulative p.1 j.val ≤ 1 - (p.2 : ℝ) ∧ 1 - (p.2 : ℝ) ≤ cumulative p.1 (j.val+1)}

theorem continuous_cumulative {n : ℕ} (k : ℕ) :
    Continuous (fun x : StdSimplex ℝ (Fin (n+1)) => cumulative x k) := by
  unfold cumulative
  apply continuous_finsetSum
  intro i hi
  split_ifs
  · exact StdSimplex.continuous_weights_apply ℝ i
  · exact continuous_const

theorem region_isClosed {n : ℕ} (j : Fin (n+1)) : IsClosed (region j) :=
  (isClosed_le ((continuous_cumulative j.val).comp continuous_fst)
    (continuous_const.sub continuous_snd.subtype_val)).inter
    (isClosed_le (continuous_const.sub continuous_snd.subtype_val)
      ((continuous_cumulative (j.val+1)).comp continuous_fst))

theorem region_cover (n : ℕ) : ⋃ j : Fin (n+1), region j = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨j, hj⟩ := exists_cut p.1 (1 - (p.2 : ℝ))
    (sub_nonneg.mpr p.2.property.2) (by linarith [p.2.property.1])
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

end Thomason.Construction.PrismBarycentric

end

section

/-! # Continuous barycentric charts for the standard prism -/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- The barycentric amount assigned to the lower copy of the cut vertex. -/
def cutMass {n : ℕ} (j : Fin (n+1))
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval) : ℝ :=
  1 - (p.2 : ℝ) - cumulative p.1 j.val

theorem cutMass_nonneg {n : ℕ} (j : Fin (n+1)) (p : region j) :
    0 ≤ cutMass j p.val := sub_nonneg.mpr p.property.1

theorem cutMass_le {n : ℕ} (j : Fin (n+1)) (p : region j) :
    cutMass j p.val ≤ p.val.1.weights j := by
  have h := p.property.2
  rw [cumulative_step] at h
  exact sub_le_iff_le_add.mpr (by simpa [add_comm] using h)

/-- The chart on the `j`th closed region, in the corresponding `(n+1)`-simplex. -/
def chart {n : ℕ} (j : Fin (n+1)) : C(region j, StdSimplex ℝ (Fin (n+2))) where
  toFun p := split p.val.1 j (cutMass j p.val) (cutMass_nonneg j p) (cutMass_le j p)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
    apply continuous_pi
    intro k
    change Continuous (fun p : region j => splitWeights p.val.1 j (cutMass j p.val) k)
    simp only [splitWeights, Finsupp.coe_add, Pi.add_apply, Finsupp.mapDomain_fintype,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, remainder,
      Finsupp.coe_sub, Pi.sub_apply]
    have hc : Continuous (fun p : region j => cumulative p.val.1 j.val) :=
      (continuous_cumulative j.val).comp (continuous_fst.comp continuous_subtype_val)
    have ha : Continuous (fun p : region j => cutMass j p.val) :=
      (continuous_const.sub (continuous_snd.comp continuous_subtype_val).subtype_val).sub hc
    apply Continuous.add
    · split_ifs
      · exact ha
      · exact continuous_const
    · apply continuous_finsetSum
      intro i hi
      split_ifs <;> fun_prop

/-- A chart has exactly the original barycentric first projection. -/
theorem chart_projection {n : ℕ} (j : Fin (n+1)) (p : region j) :
    StdSimplex.map j.predAbove (chart j p) = p.val.1 :=
  split_projection p.val.1 j (cutMass j p.val) (cutMass_nonneg j p) (cutMass_le j p)

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Boundary values of the standard prism charts -/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- The zero-mass cut lies in the face omitting its lower copy. -/
theorem split_zero {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) :
    split x j 0 le_rfl (x.weights_nonneg j) = StdSimplex.map j.castSucc.succAbove x := by
  apply StdSimplex.ext
  change splitWeights x j 0 = x.weights.mapDomain j.castSucc.succAbove
  simp [splitWeights, remainder]

/-- Away from the duplicated vertex, the two adjacent face embeddings agree. -/
theorem adjacent_embeddings {n : ℕ} (j k : Fin (n+1)) (h : k ≠ j) :
    j.castSucc.succAbove k = j.succ.succAbove k := by
  rcases lt_or_gt_of_ne h with hk | hk
  · rw [Fin.succAbove_castSucc_of_lt _ _ hk, Fin.succAbove_succ_of_le _ _ hk.le]
  · rw [Fin.succAbove_castSucc_of_le _ _ hk.le, Fin.succAbove_succ_of_lt _ _ hk]

/-- Moving the entire weight to the lower copy lies in the other face. -/
theorem split_full {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) :
    split x j (x.weights j) (x.weights_nonneg j) le_rfl = StdSimplex.map j.succ.succAbove x := by
  have hc : (remainder x j (x.weights j)).mapDomain j.castSucc.succAbove =
      (remainder x j (x.weights j)).mapDomain j.succ.succAbove := by
    apply Finsupp.mapDomain_congr
    intro k hk
    apply adjacent_embeddings j k
    intro he
    subst k
    simp [remainder] at hk
  apply StdSimplex.ext
  change splitWeights x j (x.weights j) = x.weights.mapDomain j.succ.succAbove
  unfold splitWeights
  rw [hc]
  have he : x.weights = Finsupp.single j (x.weights j) + remainder x j (x.weights j) := by
    unfold remainder
    abel
  conv_rhs => rw [he, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Fin.succAbove_succ_self]

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Realization charts and common faces of the standard prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory Convexity
open scoped Simplicial

noncomputable section

/-- The actual product of the two representable simplicial sets. -/
abbrev prism (n : ℕ) : SSet.{0} := Δ[n] ⊗ Δ[1]

/-- The `j`th maximal simplex of the standard simplicial prism. -/
abbrev simplexIndex {n : ℕ} (j : Fin (n+1)) :
    CostructuredArrow SSet.stdSimplex (prism n) :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val)

/-- Its codimension-one face at a cut between vertices. -/
abbrev faceIndex {n : ℕ} (j : Fin (n+2)) :
    CostructuredArrow SSet.stdSimplex (prism n) :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.codimOneSimplex j).val)

/-- The face omitting the upper occurrence of the cut vertex. -/
def upperFace {n : ℕ} (j : Fin (n+1)) : faceIndex j.succ ⟶ simplexIndex j :=
  CostructuredArrow.homMk (SimplexCategory.δ j.succ) (by
    change SSet.stdSimplex.map (SimplexCategory.δ j.succ) ≫
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val =
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.codimOneSimplex j.succ).val
    rw [SSet.yonedaEquiv_symm_naturality_left]
    exact congrArg SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.δ_succ_nonDegenerateEquiv j))

/-- The face omitting the lower occurrence of the cut vertex. -/
def lowerFace {n : ℕ} (j : Fin (n+1)) : faceIndex j.castSucc ⟶ simplexIndex j :=
  CostructuredArrow.homMk (SimplexCategory.δ j.castSucc) (by
    change SSet.stdSimplex.map (SimplexCategory.δ j.castSucc) ≫
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val =
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.codimOneSimplex j.castSucc).val
    rw [SSet.yonedaEquiv_symm_naturality_left]
    exact congrArg SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv j))

/-- Map a barycentric chart to the actual geometric realization of the prism. -/
def realizedChart {n : ℕ} (j : Fin (n+1)) : C(region j, SSet.toTop.obj (prism n)) where
  toFun p := (RealizationPrism.leg (prism n) (simplexIndex j)).hom (ULift.up (chart j p))
  continuous_toFun := (RealizationPrism.leg (prism n) (simplexIndex j)).hom.continuous.comp
    ((continuous_uliftUp.comp (chart j).continuous))

/-- The realized upper face is its original codimension-one realization leg. -/
theorem upperFace_value {n : ℕ} (j : Fin (n+1)) (x : StdSimplex ℝ (Fin (n+1))) :
    (RealizationPrism.leg (prism n) (simplexIndex j)).hom
      (ULift.up (StdSimplex.map j.succ.succAbove x)) =
      (RealizationPrism.leg (prism n) (faceIndex j.succ)).hom (ULift.up x) := by
  exact congrArg (fun f => f.hom (ULift.up x))
    ((RealizationPrism.cocone (prism n)).w (upperFace j))

/-- The realized lower face is its original codimension-one realization leg. -/
theorem lowerFace_value {n : ℕ} (j : Fin (n+1)) (x : StdSimplex ℝ (Fin (n+1))) :
    (RealizationPrism.leg (prism n) (simplexIndex j)).hom
      (ULift.up (StdSimplex.map j.castSucc.succAbove x)) =
      (RealizationPrism.leg (prism n) (faceIndex j.castSucc)).hom (ULift.up x) := by
  exact congrArg (fun f => f.hom (ULift.up x))
    ((RealizationPrism.cocone (prism n)).w (lowerFace j))

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Agreement of standard prism charts on all overlaps -/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

theorem cumulative_monotone {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    Monotone (cumulative x) := by
  intro k l hkl
  apply Finset.sum_le_sum
  intro i hi
  by_cases hik : i.val < k
  · have hil : i.val < l := lt_of_lt_of_le hik hkl
    simp only [ite_eq_left hik, ite_eq_left hil]
    exact le_rfl
  · simp only [ite_eq_right hik]
    split_ifs
    · exact x.weights_nonneg i
    · exact le_rfl

/-- All intermediate charts contain a point belonging to the two extreme charts. -/
theorem region_between {n : ℕ} {j k l : Fin (n+1)} (hjl : j ≤ l) (hlk : l ≤ k)
    {p : StdSimplex ℝ (Fin (n+1)) × unitInterval} (hj : p ∈ region j) (hk : p ∈ region k) :
    p ∈ region l :=
  ⟨((cumulative_monotone p.1) hlk).trans hk.1,
    hj.2.trans ((cumulative_monotone p.1) (Nat.succ_le_succ hjl))⟩

/-- Adjacent charts have equal values on their common face. -/
theorem realizedChart_adjacent {n : ℕ} (j : Fin n)
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval)
    (h₀ : p ∈ region j.castSucc) (h₁ : p ∈ region j.succ) :
    realizedChart j.castSucc ⟨p, h₀⟩ = realizedChart j.succ ⟨p, h₁⟩ := by
  have hs : 1 - (p.2 : ℝ) = cumulative p.1 (j.val+1) := le_antisymm h₀.2 h₁.1
  have hm₀ : cutMass j.castSucc p = p.1.weights j.castSucc := by
    unfold cutMass
    rw [hs]
    have hc := cumulative_step p.1 j.castSucc
    change cumulative p.1 (j.val+1) = cumulative p.1 j.val + p.1.weights j.castSucc at hc
    change cumulative p.1 (j.val+1) - cumulative p.1 j.val = _
    linarith
  have hm₁ : cutMass j.succ p = 0 := by
    unfold cutMass
    rw [hs]
    exact sub_self _
  have hc₀ : chart j.castSucc ⟨p, h₀⟩ = StdSimplex.map j.castSucc.succ.succAbove p.1 := by
    change split p.1 j.castSucc (cutMass j.castSucc p)
      (cutMass_nonneg j.castSucc ⟨p, h₀⟩) (cutMass_le j.castSucc ⟨p, h₀⟩) = _
    simpa only [hm₀] using split_full p.1 j.castSucc
  have hc₁ : chart j.succ ⟨p, h₁⟩ = StdSimplex.map j.succ.castSucc.succAbove p.1 := by
    change split p.1 j.succ (cutMass j.succ p)
      (cutMass_nonneg j.succ ⟨p, h₁⟩) (cutMass_le j.succ ⟨p, h₁⟩) = _
    simpa only [hm₁] using split_zero p.1 j.succ
  change (RealizationPrism.leg (prism n) (simplexIndex j.castSucc)).hom (ULift.up _) =
    (RealizationPrism.leg (prism n) (simplexIndex j.succ)).hom (ULift.up _)
  rw [hc₀, hc₁, upperFace_value, lowerFace_value, Fin.castSucc_succ]

/-- All charts agree, including overlaps involving zero barycentric weights. -/
theorem realizedChart_overlap_le {n : ℕ} (j k : Fin (n+1)) (hjk : j ≤ k)
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval)
    (hj : p ∈ region j) (hk : p ∈ region k) :
    realizedChart j ⟨p, hj⟩ = realizedChart k ⟨p, hk⟩ := by
  induction k using Fin.induction with
  | zero =>
    have he : j = 0 := le_antisymm hjk (Fin.zero_le _)
    subst j
    rfl
  | succ k ih =>
    by_cases h : j ≤ k.castSucc
    · have hm := region_between h k.castSucc_le_succ hj hk
      exact (ih h hm).trans (realizedChart_adjacent k p hm hk)
    · have he : j = k.succ := by
        apply Fin.ext
        change j.val = k.val+1
        have hu : j.val ≤ k.val+1 := hjk
        have hl : ¬ j.val ≤ k.val := h
        omega
      subst j
      rfl

theorem realizedChart_overlap {n : ℕ} (j k : Fin (n+1))
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval)
    (hj : p ∈ region j) (hk : p ∈ region k) :
    realizedChart j ⟨p, hj⟩ = realizedChart k ⟨p, hk⟩ := by
  rcases le_total j k with h | h
  · exact realizedChart_overlap_le j k h p hj hk
  · exact (realizedChart_overlap_le k j h p hk hj).symm

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The actual continuous standard prism in geometric realization

The finite barycentric charts agree on closed overlaps, including all
zero-weight degeneracies. They therefore glue to a continuous map from
`|Δ[n]| × I` to `|Δ[n] × Δ[1]|`.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- The actual standard prism, assembled from its maximal simplices. -/
def standardPrism (n : ℕ) :
    C(StdSimplex ℝ (Fin (n+1)) × unitInterval, SSet.toTop.obj (prism n)) where
  toFun := Set.liftCover region (fun j => realizedChart j) realizedChart_overlap (region_cover n)
  continuous_toFun := by
    apply (locallyFinite_of_finite (region (n := n))).continuous (region_cover n) region_isClosed
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (region j).domRestrict
        (Set.liftCover region (fun j => realizedChart j) realizedChart_overlap (region_cover n)) =
        realizedChart j := by
      funext x
      exact Set.liftCover_coe x
    rw [he]
    exact (realizedChart j).continuous

/-- The assembled map restricts to the originally defined chart. -/
theorem standardPrism_on_region {n : ℕ} (j : Fin (n+1))
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval) (hp : p ∈ region j) :
    standardPrism n p = realizedChart j ⟨p, hp⟩ := by
  change Set.liftCover region (fun j => realizedChart j) realizedChart_overlap (region_cover n) p = _
  exact Set.liftCover_of_mem hp

/-- At time zero the prism is its all-zero face. -/
theorem standardPrism_zero (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    standardPrism n (x, 0) =
      (RealizationPrism.leg (prism n) (faceIndex (Fin.last (n+1)))).hom (ULift.up x) := by
  have hc : cumulative x n + x.weights (Fin.last n) = 1 := by
    have h := cumulative_step x (Fin.last n)
    simpa using h.symm
  have hp : (x, (0 : unitInterval)) ∈ region (Fin.last n) := by
    constructor
    · change cumulative x n ≤ 1 - (0 : ℝ)
      have hw := x.weights_nonneg (Fin.last n)
      linarith
    · simp
  rw [standardPrism_on_region (Fin.last n) _ hp]
  have hm : cutMass (Fin.last n) (x, 0) = x.weights (Fin.last n) := by
    change 1 - (0 : ℝ) - cumulative x n = _
    linarith
  have he : chart (Fin.last n) ⟨(x, 0), hp⟩ =
      StdSimplex.map (Fin.last n).succ.succAbove x := by
    change split x (Fin.last n) (cutMass (Fin.last n) (x, 0))
      (cutMass_nonneg _ ⟨(x, 0), hp⟩) (cutMass_le _ ⟨(x, 0), hp⟩) = _
    simpa only [hm] using split_full x (Fin.last n)
  change (RealizationPrism.leg (prism n) (simplexIndex (Fin.last n))).hom (ULift.up _) = _
  rw [he, upperFace_value]
  rfl

/-- At time one the prism is its all-one face. -/
theorem standardPrism_one (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    standardPrism n (x, 1) =
      (RealizationPrism.leg (prism n) (faceIndex (0 : Fin (n+2)))).hom (ULift.up x) := by
  have hp : (x, (1 : unitInterval)) ∈ region (0 : Fin (n+1)) := by
    constructor
    · simp
    · change 1 - (1 : ℝ) ≤ cumulative x (0+1)
      have h := cumulative_step x (0 : Fin (n+1))
      have he : cumulative x 1 = x.weights 0 := by
        simpa only [Fin.val_zero, cumulative_zero, zero_add] using h
      rw [he, sub_self]
      exact x.weights_nonneg 0
  rw [standardPrism_on_region (0 : Fin (n+1)) _ hp]
  have hm : cutMass (0 : Fin (n+1)) (x, 1) = 0 := by simp [cutMass]
  have he : chart (0 : Fin (n+1)) ⟨(x, 1), hp⟩ =
      StdSimplex.map (0 : Fin (n+1)).castSucc.succAbove x := by
    change split x (0 : Fin (n+1)) (cutMass 0 (x, 1))
      (cutMass_nonneg _ ⟨(x, 1), hp⟩) (cutMass_le _ ⟨(x, 1), hp⟩) = _
    simpa only [hm] using split_zero x (0 : Fin (n+1))
  change (RealizationPrism.leg (prism n) (simplexIndex (0 : Fin (n+1)))).hom (ULift.up _) = _
  rw [he, lowerFace_value]
  rfl

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # First-projection compatibility of the actual standard prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial

noncomputable section

/-- The original representable simplex, indexed by its identity map. -/
abbrev baseIndex (n : ℕ) : CostructuredArrow SSet.stdSimplex (Δ[n] : SSet.{0}) :=
  CostructuredArrow.mk (𝟙 _)

/-- Collapsing the duplicated vertex is exactly the first prism projection. -/
def firstProjectionMap {n : ℕ} (j : Fin (n+1)) :
    (CostructuredArrow.map (fst (Δ[n] : SSet.{0}) Δ[1])).obj (simplexIndex j) ⟶ baseIndex n :=
  CostructuredArrow.homMk (SimplexCategory.σ j) (by
    change SSet.stdSimplex.map (SimplexCategory.σ j) ≫ 𝟙 _ =
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val ≫ fst _ _
    rw [Category.comp_id]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl)

/-- Every chart projects back to its original barycentric point in realization. -/
theorem realizedChart_firstProjection {n : ℕ} (j : Fin (n+1)) (p : region j) :
    (SSet.toTop.map (fst (Δ[n] : SSet.{0}) Δ[1])).hom (realizedChart j p) =
      (RealizationPrism.leg (Δ[n] : SSet.{0}) (baseIndex n)).hom (ULift.up p.val.1) := by
  have hn := congrArg (fun f => f.hom (ULift.up (chart j p)))
    (RealizationPrism.leg_naturality (fst (Δ[n] : SSet.{0}) Δ[1]) (simplexIndex j))
  have hf := congrArg (fun f => f.hom (ULift.up (chart j p)))
    ((RealizationPrism.cocone (Δ[n] : SSet.{0})).w (firstProjectionMap j))
  change _ = _ at hn
  change (RealizationPrism.leg (Δ[n] : SSet.{0}) (baseIndex n)).hom
    (ULift.up (StdSimplex.map j.predAbove (chart j p))) = _ at hf
  exact hn.trans (hf.symm.trans (congrArg
    (fun x => (RealizationPrism.leg (Δ[n] : SSet.{0}) (baseIndex n)).hom (ULift.up x))
    (chart_projection j p)))

/-- The assembled prism has the prescribed first projection at every point. -/
theorem standardPrism_firstProjection (n : ℕ)
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval) :
    (SSet.toTop.map (fst (Δ[n] : SSet.{0}) Δ[1])).hom (standardPrism n p) =
      (RealizationPrism.leg (Δ[n] : SSet.{0}) (baseIndex n)).hom (ULift.up p.1) := by
  have hp : p ∈ ⋃ j : Fin (n+1), region j := by rw [region_cover]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
  rw [standardPrism_on_region j p hj]
  exact realizedChart_firstProjection j ⟨p, hj⟩

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The two actual simplicial endpoints of the standard realization prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory Convexity
open scoped Simplicial

noncomputable section

theorem zeroFace_hom (n : ℕ) :
    (faceIndex (Fin.last (n+1))).hom = SSet.ι₀ (X := (Δ[n] : SSet.{0})) := by
  apply SSet.yonedaEquiv.injective
  change (SSet.prodStdSimplex₁.codimOneSimplex (Fin.last (n+1))).val = _
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext k
    change ((SSet.stdSimplex.objMk₁.{0} (Fin.last (n+1))) k : Fin 2).val = (0 : Fin 2).val
    exact congrArg Fin.val (SSet.stdSimplex.objMk₁_of_castSucc_lt.{0} _ k (Fin.castSucc_lt_last k))

theorem oneFace_hom (n : ℕ) :
    (faceIndex (0 : Fin (n+2))).hom = SSet.ι₁ (X := (Δ[n] : SSet.{0})) := by
  apply SSet.yonedaEquiv.injective
  change (SSet.prodStdSimplex₁.codimOneSimplex (0 : Fin (n+2))).val = _
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext k
    change ((SSet.stdSimplex.objMk₁.{0} (0 : Fin (n+2))) k : Fin 2).val = (1 : Fin 2).val
    exact congrArg Fin.val (SSet.stdSimplex.objMk₁_of_le_castSucc.{0} _ k (Fin.zero_le _))

/-- The standard prism expressed in the exact topological-simplex convention
used by the realization colimit (including its universe lift). -/
def liftedStandardPrism (n : ℕ) :
    TopologicalInterval.cylinder.obj (SimplexCategory.toTop.{0}.obj (.mk n)) ⟶
      SSet.toTop.obj (prism n) :=
  TopCat.ofHom ((standardPrism n).comp ⟨fun p => (p.1.down, p.2), by fun_prop⟩)

/-- At zero, the continuous prism is exactly realization of the simplicial
zero endpoint, preceded by the canonical representable comparison. -/
theorem liftedStandardPrism_zero (n : ℕ) :
    TopologicalInterval.sectionAt (SimplexCategory.toTop.{0}.obj (.mk n)) 0 ≫
      liftedStandardPrism n = SSet.toTopSimplex.inv.app (.mk n) ≫ SSet.toTop.map SSet.ι₀ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have h := standardPrism_zero n x.down
  change standardPrism n (x.down, 0) = _
  rw [h]
  change (SSet.toTopSimplex.inv.app (.mk n) ≫
    SSet.toTop.map (faceIndex (Fin.last (n+1))).hom).hom x = _
  rw [zeroFace_hom]

/-- The analogous equality at the one endpoint. -/
theorem liftedStandardPrism_one (n : ℕ) :
    TopologicalInterval.sectionAt (SimplexCategory.toTop.{0}.obj (.mk n)) 1 ≫
      liftedStandardPrism n = SSet.toTopSimplex.inv.app (.mk n) ≫ SSet.toTop.map SSet.ι₁ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have h := standardPrism_one n x.down
  change standardPrism n (x.down, 1) = _
  rw [h]
  change (SSet.toTopSimplex.inv.app (.mk n) ≫
    SSet.toTop.map (faceIndex (0 : Fin (n+2))).hom).hom x = _
  rw [oneFace_hom]

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Cumulative mass under ordinal maps

These identities include noninjective ordinal maps. They show that every
prism chart maps into the chart indexed by the image of its cut vertex.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

/-- Pushforward barycentric mass below a threshold is the mass of its preimage. -/
theorem cumulative_map {m n : ℕ} (f : Fin (m+1) → Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (k : ℕ) :
    cumulative (StdSimplex.map f x) k =
      ∑ i : Fin (m+1), if (f i).val < k then x.weights i else 0 := by
  classical
  unfold cumulative
  rw [← Finsupp.sum_fintype (StdSimplex.map f x).weights
    (fun i a => if i.val < k then a else 0) (by intro i; split_ifs <;> rfl)]
  change (x.weights.mapDomain f).sum (fun i a => if i.val < k then a else 0) = _
  rw [Finsupp.sum_mapDomain_index (by intro i; split_ifs <;> rfl)
    (by intro i a b; split_ifs <;> simp)]
  exact Finsupp.sum_fintype _ _ (by intro; simp)

/-- No vertex at or after the cut maps strictly below its image cut. -/
theorem cumulative_map_lower {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) :
    cumulative (StdSimplex.map f x) (f j).val ≤ cumulative x j.val := by
  rw [cumulative_map]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hf : (f i).val < (f j).val
  · have hij : i.val < j.val := by
      by_contra! hh
      have hm := f.monotone hh
      exact (not_lt_of_ge hm) hf
    simp only [ite_eq_left hf, ite_eq_left hij]
    exact le_rfl
  · simp only [ite_eq_right hf]
    split_ifs
    · exact x.weights_nonneg i
    · exact le_rfl

/-- Every vertex up to the cut maps to a vertex up to its image. -/
theorem cumulative_map_upper {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) :
    cumulative x (j.val+1) ≤ cumulative (StdSimplex.map f x) ((f j).val+1) := by
  rw [cumulative_map]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hij : i.val < j.val+1
  · have hf : (f i).val < (f j).val+1 := by
      have hm := f.monotone (show i ≤ j from by omega)
      omega
    simp only [ite_eq_left hij, ite_eq_left hf]
    exact le_rfl
  · simp only [ite_eq_right hij]
    split_ifs
    · exact x.weights_nonneg i
    · exact le_rfl

/-- The image of a closed prism region belongs to the corresponding image region. -/
theorem region_map {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1))
    (p : region j) : (StdSimplex.map f p.val.1, p.val.2) ∈ region (f j) :=
  ⟨(cumulative_map_lower f p.val.1 j).trans p.property.1,
    p.property.2.trans (cumulative_map_upper f p.val.1 j)⟩

end Thomason.Construction.PrismBarycentric

end

section

/-! # Ordinal maps between the actual maximal prism simplices

The cut vertex maps to its image even when the ordinal map is degenerate.
The first-coordinate and side-of-cut identities are proved explicitly.
-/

namespace Thomason.Construction.PrismBarycentric

def prismOrdinal {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1)) :
    Fin (m+2) →o Fin (n+2) where
  toFun k := if k ≤ j.castSucc then (f (j.predAbove k)).castSucc else (f (j.predAbove k)).succ
  monotone' a b hab := by
    have hf := f.monotone (j.predAbove_right_monotone hab)
    dsimp
    split_ifs with ha hb hb
    · exact Fin.castSucc_le_castSucc_iff.mpr hf
    · change (f (j.predAbove a)).val ≤ (f (j.predAbove b)).val+1
      have hv : (f (j.predAbove a)).val ≤ (f (j.predAbove b)).val := hf
      omega
    · exact False.elim (ha (hab.trans hb))
    · exact Fin.succ_le_succ_iff.mpr hf

@[simp]
theorem prismOrdinal_apply {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1))
    (k : Fin (m+2)) : prismOrdinal f j k =
      if k ≤ j.castSucc then (f (j.predAbove k)).castSucc else (f (j.predAbove k)).succ := rfl

theorem predAbove_le_cut {m : ℕ} (j : Fin (m+1)) {k : Fin (m+2)}
    (hk : k ≤ j.castSucc) : j.predAbove k ≤ j := by
  simpa only [Fin.predAbove_castSucc_self] using j.predAbove_right_monotone hk

theorem cut_le_predAbove {m : ℕ} (j : Fin (m+1)) {k : Fin (m+2)}
    (hk : j.castSucc < k) : j ≤ j.predAbove k := by
  have hs : j.succ ≤ k := by
    change j.val+1 ≤ k.val
    exact hk
  simpa only [Fin.predAbove_succ_self] using j.predAbove_right_monotone hs

/-- The first coordinate is exactly the original ordinal map. -/
theorem prismOrdinal_first {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1))
    (k : Fin (m+2)) :
    (f j).predAbove (prismOrdinal f j k) = f (j.predAbove k) := by
  by_cases hk : k ≤ j.castSucc
  · simp only [prismOrdinal_apply, ite_eq_left hk]
    exact Fin.predAbove_castSucc_of_le _ _ (f.monotone (predAbove_le_cut j hk))
  · simp only [prismOrdinal_apply, ite_eq_right hk]
    exact Fin.predAbove_succ_of_le _ _ (f.monotone (cut_le_predAbove j (lt_of_not_ge hk)))

/-- Both ends of the doubled cut stay on their prescribed sides. -/
theorem prismOrdinal_cut {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1))
    (k : Fin (m+2)) :
    prismOrdinal f j k ≤ (f j).castSucc ↔ k ≤ j.castSucc := by
  by_cases hk : k ≤ j.castSucc
  · simp only [prismOrdinal_apply, hk, iff_true]
    exact Fin.castSucc_le_castSucc_iff.mpr (f.monotone (predAbove_le_cut j hk))
  · simp only [prismOrdinal_apply, hk, iff_false]
    have h := f.monotone (cut_le_predAbove j (lt_of_not_ge hk))
    change ¬ (f (j.predAbove k)).val+1 ≤ (f j).val
    have hv : (f j).val ≤ (f (j.predAbove k)).val := h
    omega

end Thomason.Construction.PrismBarycentric

end

section

/-! # Compatibility of prism simplices with every ordinal map -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- The lifted ordinal map is an actual map between the corresponding
simplices of the simplicial prism, including degenerate ordinal maps. -/
def simplexNaturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1)) :
    (CostructuredArrow.map (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1])).obj
      (simplexIndex j) ⟶ simplexIndex (f j) :=
  CostructuredArrow.homMk (SimplexCategory.Hom.mk (prismOrdinal f j)) (by
    change SSet.stdSimplex.map (SimplexCategory.Hom.mk (prismOrdinal f j)) ≫
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv (f j)).val =
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val ≫
        (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1])
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_comp]
    change (prism n).map (Quiver.Hom.op (show SimplexCategory.mk (m+1) ⟶ SimplexCategory.mk (n+1) from
      SimplexCategory.Hom.mk (prismOrdinal f j)))
      (SSet.prodStdSimplex₁.nonDegenerateEquiv (f j)).val =
      (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1]).app _
        (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val
    apply Prod.ext
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      exact congrArg Fin.val (prismOrdinal_first f j k)
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      change (if (prismOrdinal f j k).castSucc < (f j).succ.castSucc then (0 : Fin 2) else 1).val =
        (if k.castSucc < j.succ.castSucc then (0 : Fin 2) else 1).val
      have h := prismOrdinal_cut f j k
      have hc : (prismOrdinal f j k).castSucc < (f j).succ.castSucc ↔
          k.castSucc < j.succ.castSucc := by
        change (prismOrdinal f j k).val < (f j).val+1 ↔ k.val < j.val+1
        change (prismOrdinal f j k).val ≤ (f j).val ↔ k.val ≤ j.val at h
        omega
      simp only [hc])

end

end Thomason.Construction.PrismBarycentric

end

end OAI
