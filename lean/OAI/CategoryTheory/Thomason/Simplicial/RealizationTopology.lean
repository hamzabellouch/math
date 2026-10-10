import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Order
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order.Lattice

namespace OAI

section

/-! # Barycentric retraction onto the geometric horn

Subtract the smallest non-cone coordinate from every such coordinate and
move the removed mass to the cone vertex. This continuous retraction fixes
the entire horn pointwise, as needed for relative horn attachments.
-/

namespace Thomason.Construction.HornBarycentric

open Convexity

noncomputable section

/-- The vertices other than the horn's cone vertex. -/
def others {n : ℕ} (i : Fin (n+2)) : Finset (Fin (n+2)) := Finset.univ.erase i

theorem others_nonempty {n : ℕ} (i : Fin (n+2)) : (others i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, by simp [others, hj]⟩

/-- The smallest coordinate away from the cone vertex. -/
def mass {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) : ℝ :=
  (others i).inf' (others_nonempty i) x.weights

theorem mass_nonneg {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    0 ≤ mass i x := Finset.le_inf' _ _ (fun j _ => x.weights_nonneg j)

theorem mass_le {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2)))
    {j : Fin (n+2)} (hj : j ≠ i) : mass i x ≤ x.weights j :=
  Finset.inf'_le _ (by simp [others, hj])

theorem mass_attained {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    ∃ j, j ≠ i ∧ mass i x = x.weights j := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' (others_nonempty i) x.weights
  exact ⟨j, (Finset.mem_erase.mp hj).1, he⟩

theorem continuous_mass {n : ℕ} (i : Fin (n+2)) : Continuous (mass i) :=
  Continuous.finset_inf'_apply (others_nonempty i)
    (fun j _ => StdSimplex.continuous_weights_apply ℝ j)

/-- Coordinates after shifting a nonnegative amount of mass to the cone vertex. -/
def shiftedWeights {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) (a : ℝ) :
    Fin (n+2) →₀ ℝ :=
  Finsupp.onFinset Finset.univ
    (fun j => if j = i then x.weights j + (n+1 : ℝ)*a else x.weights j-a)
    (by simp)

/-- Every shift up to the minimum coordinate remains a barycentric point. -/
def shift {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2)))
    (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ mass i x) : StdSimplex ℝ (Fin (n+2)) where
  weights := shiftedWeights i x a
  nonneg := by
    intro j
    change 0 ≤ if j = i then x.weights j + (n+1 : ℝ)*a else x.weights j-a
    split_ifs with hj
    · exact add_nonneg (x.weights_nonneg j) (mul_nonneg (by positivity) ha)
    · exact sub_nonneg.mpr (hb.trans (mass_le i x hj))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ j : Fin (n+2), if j = i then x.weights j + (n+1 : ℝ)*a else x.weights j-a) = 1
    have he (j : Fin (n+2)) :
        (if j = i then x.weights j + (n+1 : ℝ)*a else x.weights j-a) =
        x.weights j-a + (if j = i then (n+2 : ℝ)*a else 0) := by
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have ht : ∑ j : Fin (n+2), x.weights j = 1 := by
      have ht := x.total
      rw [Finsupp.sum_fintype _ _ (by simp)] at ht
      exact ht
    rw [ht]
    simp

/-- The geometric horn is the union of all faces except the opposite face. -/
def horn {n : ℕ} (i : Fin (n+2)) : Set (StdSimplex ℝ (Fin (n+2))) :=
  {x | ∃ j, j ≠ i ∧ x.weights j = 0}

/-- Subtracting the minimum lands in the geometric horn. -/
theorem shift_mass_mem {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    shift i x (mass i x) (mass_nonneg i x) le_rfl ∈ horn i := by
  obtain ⟨j, hj, he⟩ := mass_attained i x
  refine ⟨j, hj, ?_⟩
  change (if j = i then x.weights j + (n+1 : ℝ)*mass i x else x.weights j-mass i x) = 0
  simp [hj, he]

/-- On the geometric horn the minimum coordinate is zero. -/
theorem mass_eq_zero {n : ℕ} (i : Fin (n+2)) {x : StdSimplex ℝ (Fin (n+2))}
    (hx : x ∈ horn i) : mass i x = 0 := by
  obtain ⟨j, hj, hz⟩ := hx
  exact le_antisymm ((mass_le i x hj).trans_eq hz) (mass_nonneg i x)

@[simp]
theorem shift_zero {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    shift i x 0 le_rfl (mass_nonneg i x) = x := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (if j = i then x.weights j + (n+1 : ℝ)*0 else x.weights j-0) = x.weights j
  split_ifs <;> simp

/-- The actual continuous retraction to the geometric horn. -/
def retraction {n : ℕ} (i : Fin (n+2)) : C(StdSimplex ℝ (Fin (n+2)), horn i) where
  toFun x := ⟨shift i x (mass i x) (mass_nonneg i x) le_rfl, shift_mass_mem i x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
    apply continuous_pi
    intro j
    change Continuous (fun x : StdSimplex ℝ (Fin (n+2)) =>
      if j = i then x.weights j + (n+1 : ℝ)*mass i x else x.weights j-mass i x)
    split_ifs
    · exact (StdSimplex.continuous_weights_apply ℝ j).add
        (continuous_const.mul (continuous_mass i))
    · exact (StdSimplex.continuous_weights_apply ℝ j).sub (continuous_mass i)

/-- The retraction fixes the whole horn, including every overlap of faces. -/
theorem retraction_fixed {n : ℕ} (i : Fin (n+2)) (x : horn i) :
    (retraction i x.val).val = x.val := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (if j = i then x.val.weights j + (n+1 : ℝ)*mass i x.val
    else x.val.weights j-mass i x.val) = x.val.weights j
  rw [mass_eq_zero i x.property]
  split_ifs <;> simp

/-- Shift only the fraction of mass specified by the interval coordinate. -/
def deformation {n : ℕ} (i : Fin (n+2)) :
    C(StdSimplex ℝ (Fin (n+2)) × unitInterval, StdSimplex ℝ (Fin (n+2))) where
  toFun p := shift i p.1 ((p.2 : ℝ) * mass i p.1)
    (mul_nonneg p.2.property.1 (mass_nonneg i p.1))
    (mul_le_of_le_one_left (mass_nonneg i p.1) p.2.property.2)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
    apply continuous_pi
    intro j
    change Continuous (fun p : StdSimplex ℝ (Fin (n+2)) × unitInterval =>
      if j = i then p.1.weights j + (n+1 : ℝ)*((p.2 : ℝ)*mass i p.1)
      else p.1.weights j-(p.2 : ℝ)*mass i p.1)
    have hc : Continuous (fun p : StdSimplex ℝ (Fin (n+2)) × unitInterval =>
        (p.2 : ℝ)*mass i p.1) :=
      continuous_snd.subtype_val.mul ((continuous_mass i).comp continuous_fst)
    split_ifs
    · exact ((StdSimplex.continuous_weights_apply ℝ j).comp continuous_fst).add
        (continuous_const.mul hc)
    · exact ((StdSimplex.continuous_weights_apply ℝ j).comp continuous_fst).sub hc

@[simp]
theorem deformation_zero {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    deformation i (x, 0) = x := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (if j = i then x.weights j + (n+1 : ℝ)*(0*mass i x)
    else x.weights j-0*mass i x) = x.weights j
  split_ifs <;> simp

@[simp]
theorem deformation_one {n : ℕ} (i : Fin (n+2)) (x : StdSimplex ℝ (Fin (n+2))) :
    deformation i (x, 1) = (retraction i x).val := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (if j = i then x.weights j + (n+1 : ℝ)*(1*mass i x)
    else x.weights j-1*mass i x) = _
  simp only [one_mul]
  rfl

/-- The entire deformation is stationary on the geometric horn. -/
theorem deformation_fixed {n : ℕ} (i : Fin (n+2)) (x : horn i) (t : unitInterval) :
    deformation i (x.val, t) = x.val := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (if j = i then x.val.weights j + (n+1 : ℝ)*((t : ℝ)*mass i x.val)
    else x.val.weights j-(t : ℝ)*mass i x.val) = x.val.weights j
  rw [mass_eq_zero i x.property]
  split_ifs <;> simp

end

end Thomason.Construction.HornBarycentric

end

section

/-! # Deleting a zero barycentric coordinate

A monotone degeneracy supplies a continuous inverse on each face of a
standard simplex, including its last face. These are the local charts for
identifying the geometric horn with the realization of the simplicial horn.
-/

namespace Thomason.Construction.HornBarycentric

open Convexity

noncomputable section

/-- A monotone deletion map, with an arbitrary choice only at the deleted vertex. -/
def deletion {n : ℕ} (j : Fin (n+2)) : Fin (n+2) →o Fin (n+1) :=
  Fin.cases (SimplexCategory.σ (0 : Fin (n+1))).toOrderHom
    (fun k => (SimplexCategory.σ k).toOrderHom) j

/-- Reinserting the deleted coordinate is the identity away from it. -/
theorem insertion_deletion {n : ℕ} (j k : Fin (n+2)) (hk : k ≠ j) :
    j.succAbove (deletion j k) = k := by
  induction j using Fin.cases with
  | zero =>
    change (0 : Fin (n+2)).succAbove ((0 : Fin (n+1)).predAbove k) = k
    rw [Fin.succAbove_zero]
    exact Fin.succ_predAbove_zero hk
  | succ j =>
    exact Fin.succ_succAbove_predAbove hk

@[simp]
theorem deletion_insertion {n : ℕ} (j : Fin (n+2)) (k : Fin (n+1)) :
    deletion j (j.succAbove k) = k := by
  apply Fin.succAbove_right_injective
  exact insertion_deletion j _ (Fin.succAbove_ne j k)

/-- Injective vertex maps remain injective on barycentric points. -/
theorem simplex_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro x y h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hf (congrArg StdSimplex.weights h)

/-- Inserting after deleting a zero coordinate recovers the original point. -/
theorem face_recover {n : ℕ} (j : Fin (n+2))
    (x : StdSimplex ℝ (Fin (n+2))) (hx : x.weights j = 0) :
    StdSimplex.map j.succAbove (StdSimplex.map (deletion j) x) = x := by
  apply StdSimplex.ext
  change (x.weights.mapDomain (deletion j)).mapDomain j.succAbove = x.weights
  rw [← Finsupp.mapDomain_comp]
  have he : x.weights.mapDomain (j.succAbove ∘ deletion j) = x.weights.mapDomain id := by
    apply Finsupp.mapDomain_congr
    intro k hk
    exact insertion_deletion j k (by
      intro hj
      subst k
      exact (Finsupp.mem_support_iff.mp hk) hx)
  exact he.trans (Finsupp.mapDomain_id)

/-- Deletion is the inverse on the entire face chart. -/
theorem face_delete_insert {n : ℕ} (j : Fin (n+2))
    (x : StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (deletion j) (StdSimplex.map j.succAbove x) = x := by
  rw [← StdSimplex.map_comp]
  have he : (deletion j) ∘ j.succAbove = id := by
    funext k
    exact deletion_insertion j k
  rw [he, StdSimplex.map_id]

end

end Thomason.Construction.HornBarycentric

end

section

/-! # A barycentric point represented on its ordered support

This finite support representation compares different face charts without
assuming injectivity of a realization map.
-/

namespace Thomason.Construction.HornBarycentric

open Convexity

noncomputable section

theorem support_nonempty {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    x.weights.support.Nonempty := by
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  have ht := x.total
  rw [h] at ht
  simp at ht

def supportLen {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) : ℕ := x.weights.support.card-1

theorem support_card {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    x.weights.support.card = supportLen x+1 := by
  have h := Finset.card_pos.mpr (support_nonempty x)
  unfold supportLen
  omega

/-- The increasing enumeration of the nonzero coordinates. -/
def supportMap {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    Fin (supportLen x+1) ↪o Fin (n+1) := x.weights.support.orderEmbOfFin (support_card x)

theorem supportMap_mem {n : ℕ} (x : StdSimplex ℝ (Fin (n+1)))
    (k : Fin (supportLen x+1)) : supportMap x k ∈ x.weights.support :=
  Finset.orderEmbOfFin_mem _ _ _

theorem supportMap_ne {n : ℕ} (x : StdSimplex ℝ (Fin (n+1)))
    {j : Fin (n+1)} (hj : x.weights j = 0) (k : Fin (supportLen x+1)) : supportMap x k ≠ j := by
  intro he
  have h := Finsupp.mem_support_iff.mp (supportMap_mem x k)
  exact h (he ▸ hj)

/-- Coordinates on the ordered support. -/
def supportCoordinates {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    StdSimplex ℝ (Fin (supportLen x+1)) := StdSimplex.map (Function.invFun (supportMap x)) x

/-- Reinsert the support coordinates to recover the original point. -/
theorem support_recover {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (supportMap x) (supportCoordinates x) = x := by
  apply StdSimplex.ext
  change (x.weights.mapDomain (Function.invFun (supportMap x))).mapDomain (supportMap x) = x.weights
  rw [← Finsupp.mapDomain_comp]
  have he : x.weights.mapDomain ((supportMap x) ∘ Function.invFun (supportMap x)) =
      x.weights.mapDomain id := by
    apply Finsupp.mapDomain_congr
    intro k hk
    have hr : k ∈ Set.range (supportMap x) := by
      rw [supportMap, Finset.range_orderEmbOfFin]
      exact hk
    obtain ⟨l, rfl⟩ := hr
    change supportMap x (Function.invFun (supportMap x) (supportMap x l)) = supportMap x l
    rw [Function.leftInverse_invFun (supportMap x).injective]
  exact he.trans Finsupp.mapDomain_id

/-- A face chart receives exactly the support coordinates via its face map. -/
theorem support_delete {n : ℕ} (x : StdSimplex ℝ (Fin (n+2))) (j : Fin (n+2)) :
    StdSimplex.map ((deletion j).comp (supportMap x).toOrderHom) (supportCoordinates x) =
      StdSimplex.map (deletion j) x := by
  change StdSimplex.map ((deletion j) ∘ (supportMap x)) (supportCoordinates x) = _
  rw [StdSimplex.map_comp, support_recover]

end

end Thomason.Construction.HornBarycentric

end

section

/-! # Ordered barycentric supports under arbitrary simplex operators -/

namespace Thomason.Construction.HornBarycentric

open Convexity

noncomputable section

theorem supportMap_range {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    Set.range (supportMap x) = (x.weights.support : Set (Fin (n+1))) := by
  exact Finset.range_orderEmbOfFin _ _

theorem support_map {m n : ℕ} (f : Fin (m+1) → Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) :
    (StdSimplex.map f x).weights.support = x.weights.support.image f :=
  Finsupp.support_mapDomain_of_nonneg x.nonneg f

theorem map_supportMap_mem {m n : ℕ} (f : Fin (m+1) → Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (k : Fin (supportLen x+1)) :
    f (supportMap x k) ∈ (StdSimplex.map f x).weights.support := by
  rw [support_map]
  exact Finset.mem_image.mpr ⟨supportMap x k, supportMap_mem x k, rfl⟩

/-- Restriction of an ordinal map to the ordered supports of a barycentric point and its image. -/
def supportOrdinal {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) :
    Fin (supportLen x+1) →o Fin (supportLen (StdSimplex.map f x)+1) where
  toFun k := Function.invFun (supportMap (StdSimplex.map f x)) (f (supportMap x k))
  monotone' a b hab := by
    apply (supportMap (StdSimplex.map f x)).le_iff_le.mp
    have he (k : Fin (supportLen x+1)) :
        supportMap (StdSimplex.map f x)
          (Function.invFun (supportMap (StdSimplex.map f x)) (f (supportMap x k))) =
            f (supportMap x k) := by
      apply Function.invFun_eq
      change f (supportMap x k) ∈ Set.range (supportMap (StdSimplex.map f x))
      rw [supportMap_range]
      exact map_supportMap_mem f x k
    rw [he, he]
    exact f.monotone ((supportMap x).monotone hab)

/-- The support square commutes even when the original operator is degenerate. -/
theorem supportOrdinal_commutes {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (k : Fin (supportLen x+1)) :
    supportMap (StdSimplex.map f x) (supportOrdinal f x k) = f (supportMap x k) := by
  apply Function.invFun_eq
  change f (supportMap x k) ∈ Set.range (supportMap (StdSimplex.map f x))
  rw [supportMap_range]
  exact map_supportMap_mem f x k

/-- Every supported target vertex comes from a supported source vertex. -/
theorem supportOrdinal_surjective {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) : Function.Surjective (supportOrdinal f x) := by
  intro j
  have hj := supportMap_mem (StdSimplex.map f x) j
  rw [support_map] at hj
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hj
  have hr : a ∈ Set.range (supportMap x) := by rw [supportMap_range]; exact ha
  obtain ⟨k, rfl⟩ := hr
  refine ⟨k, (supportMap (StdSimplex.map f x)).injective ?_⟩
  rw [supportOrdinal_commutes]
  exact he


/-- Coordinates on the ordered support commute with the induced support operator. -/
theorem supportCoordinates_naturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) :
    StdSimplex.map (supportOrdinal f x) (supportCoordinates x) =
      supportCoordinates (StdSimplex.map f x) := by
  apply simplex_map_injective (supportMap (StdSimplex.map f x)).injective
  rw [← StdSimplex.map_comp, support_recover]
  have he : (supportMap (StdSimplex.map f x)) ∘ (supportOrdinal f x) =
      f ∘ (supportMap x) := funext (supportOrdinal_commutes f x)
  rw [he, StdSimplex.map_comp, support_recover]

end

end Thomason.Construction.HornBarycentric

end

section

/-! # Face charts into the actual realization of a horn

Each zero-coordinate face maps through the corresponding simplicial face.
The ordered support gives a common simplex proving all chart overlaps.
-/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- An actual codimension-one simplex of the horn. -/
abbrev faceIndex {n : ℕ} (i j : Fin (n+2)) (hj : j ≠ i) :
    CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0}) :=
  CostructuredArrow.mk (SSet.horn.ι i j hj)

/-- The simplex on the ordered support of a point of the geometric horn. -/
def supportHom {n : ℕ} (i : Fin (n+2)) (x : horn i) :
    (Δ[supportLen x.val] : SSet.{0}) ⟶ Λ[n+1, i] :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map
    (SimplexCategory.Hom.mk (supportMap x.val).toOrderHom)) (by
      intro m s hs
      obtain ⟨y, rfl⟩ := hs
      obtain ⟨j, hj, hz⟩ := x.property
      apply (SSet.mem_horn_iff_notMem_range _ i).mpr
      refine ⟨j, hj, ?_⟩
      rintro ⟨k, hk⟩
      exact supportMap_ne x.val hz ((SSet.stdSimplex.objEquiv y).toOrderHom k) hk)

abbrev supportIndex {n : ℕ} (i : Fin (n+2)) (x : horn i) :
    CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0}) :=
  CostructuredArrow.mk (supportHom i x)

/-- Support inclusion factors through every zero-coordinate face. -/
def supportToFace {n : ℕ} (i j : Fin (n+2)) (hj : j ≠ i)
    (x : horn i) (hx : x.val.weights j = 0) : supportIndex i x ⟶ faceIndex i j hj :=
  CostructuredArrow.homMk
    (SimplexCategory.Hom.mk ((deletion j).comp (supportMap x.val).toOrderHom)) (by
      apply (cancel_mono (Λ[n+1, i].ι : _ ⟶ (Δ[n+1] : SSet.{0}))).mp
      change (SSet.stdSimplex.map
        (SimplexCategory.Hom.mk ((deletion j).comp (supportMap x.val).toOrderHom)) ≫
          SSet.horn.ι i j hj) ≫ Λ[n+1, i].ι = supportHom i x ≫ Λ[n+1, i].ι
      rw [Category.assoc, SSet.horn.ι_ι]
      change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = SSet.stdSimplex.map _
      rw [← Functor.map_comp]
      congr 1
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro k
      exact insertion_deletion j _ (supportMap_ne x.val hx k))

/-- The local chart on a chosen zero coordinate, with values in the actual realization. -/
def faceValue {n : ℕ} (i j : Fin (n+2)) (hj : j ≠ i)
    (x : StdSimplex ℝ (Fin (n+2))) : SSet.toTop.obj (Λ[n+1, i] : SSet.{0}) :=
  (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) (faceIndex i j hj)).hom
    (ULift.up (StdSimplex.map (deletion j) x))

/-- All face charts take the canonical support value wherever they apply. -/
theorem faceValue_support {n : ℕ} (i j : Fin (n+2)) (hj : j ≠ i)
    (x : horn i) (hx : x.val.weights j = 0) :
    faceValue i j hj x.val =
      (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) (supportIndex i x)).hom
        (ULift.up (supportCoordinates x.val)) := by
  have h := congrArg (fun f => f.hom (ULift.up (supportCoordinates x.val)))
    ((RealizationPrism.cocone (Λ[n+1, i] : SSet.{0})).w (supportToFace i j hj x hx))
  change (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) (faceIndex i j hj)).hom
    (ULift.up (StdSimplex.map ((deletion j).comp (supportMap x.val).toOrderHom)
      (supportCoordinates x.val))) = _ at h
  rw [support_delete] at h
  exact h

/-- The local face charts agree on every intersection, including degenerate points. -/
theorem faceValue_overlap {n : ℕ} (i j k : Fin (n+2)) (hj : j ≠ i) (hk : k ≠ i)
    (x : StdSimplex ℝ (Fin (n+2))) (hxj : x.weights j = 0) (hxk : x.weights k = 0) :
    faceValue i j hj x = faceValue i k hk x := by
  let p : horn i := ⟨x, j, hj, hxj⟩
  exact (faceValue_support i j hj p hxj).trans (faceValue_support i k hk p hxk).symm

end

end Thomason.Construction.HornBarycentric

end

section

/-! # Kan fibres over a simplicial deformation of the base -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The actual simplicial fibre over a vertex, in all degrees. -/
def simplicialPointFiber {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌) : E.Subcomplex :=
  (SSet.Subcomplex.ofSimplex b).preimage p

@[reassoc]
theorem simplicialPointFiber_ι_comp {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (simplicialPointFiber p b).ι ≫ p = SSet.const b := by
  change ((SSet.Subcomplex.ofSimplex b).preimage p).ι ≫ p = _
  rw [← SSet.Subcomplex.fromPreimage_ι, SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
  rfl

/-- A map with constant projection factors through the literal point fibre. -/
def simplicialPointFiberLift {K E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : K ⟶ E) (hf : f ≫ p = SSet.const b) : K ⟶ (simplicialPointFiber p b).toSSet :=
  SSet.Subcomplex.lift f (by
    intro d z hz
    obtain ⟨u, rfl⟩ := hz
    change (f ≫ p).app d u ∈ (SSet.Subcomplex.ofSimplex b).obj d
    rw [hf]
    exact ⟨_, rfl⟩)

@[reassoc]
theorem simplicialPointFiberLift_ι {K E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : K ⟶ E) (hf : f ≫ p = SSet.const b) :
    simplicialPointFiberLift p b f hf ≫ (simplicialPointFiber p b).ι = f := rfl

/-- Lift a contraction of the base to a stationary deformation onto the
actual point fibre. The stationarity premise is the exact cylinder equality
on that fibre, not a weak-equivalence or lifting assumption. -/
theorem kan_fiber_deformation {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (b : B _⦋0⦌)
    (H : SSet.Homotopy (𝟙 B) (SSet.const b))
    (hs : ((simplicialPointFiber p b).ι ≫ p) ▷ Δ[1] ≫ H.h =
      fst (simplicialPointFiber p b).toSSet Δ[1] ≫ (simplicialPointFiber p b).ι ≫ p) :
    ∃ r : E ⟶ (simplicialPointFiber p b).toSSet,
      (simplicialPointFiber p b).ι ≫ r = 𝟙 _ ∧
      ∃ T : SSet.Homotopy (𝟙 E) (r ≫ (simplicialPointFiber p b).ι),
        (simplicialPointFiber p b).ι ▷ Δ[1] ≫ T.h =
          fst (simplicialPointFiber p b).toSSet Δ[1] ≫ (simplicialPointFiber p b).ι ∧
        T.h ≫ p = p ▷ Δ[1] ≫ H.h := by
  let F := simplicialPointFiber p b
  let c := fst F.toSSet (Δ[1] : SSet.{0}) ≫ F.ι
  let d := p ▷ (Δ[1] : SSet.{0}) ≫ H.h
  have hc : SSet.ι₀ ≫ c = F.ι ≫ 𝟙 E := by
    simp only [c, ← Category.assoc, SSet.ι₀_fst, Category.id_comp, Category.comp_id]
  have hd : c ≫ p = F.ι ▷ Δ[1] ≫ d := by
    dsimp only [c, d]
    calc
      (fst F.toSSet Δ[1] ≫ F.ι) ≫ p = fst F.toSSet Δ[1] ≫ F.ι ≫ p :=
        Category.assoc _ _ _
      _ = ((F.ι ≫ p) ▷ Δ[1]) ≫ H.h := hs.symm
      _ = (F.ι ▷ Δ[1] ≫ p ▷ Δ[1]) ≫ H.h :=
        congrArg (fun q => q ≫ H.h) (comp_whiskerRight F.ι p Δ[1])
      _ = F.ι ▷ Δ[1] ≫ p ▷ Δ[1] ≫ H.h := Category.assoc _ _ _
  have h₀ : 𝟙 E ≫ p = SSet.ι₀ ≫ d := by
    dsimp only [d]
    have hn : SSet.ι₀ ≫ p ▷ Δ[1] = p ≫ SSet.ι₀ := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, H.h₀, Category.comp_id, Category.id_comp]
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_cylinder_lift F.ι p (𝟙 E) c d hc hd h₀
  let f := SSet.ι₁ ≫ e
  have hf : f ≫ p = SSet.const b := by
    dsimp only [f]
    rw [Category.assoc, hep]
    dsimp only [d]
    have hn : SSet.ι₁ ≫ p ▷ Δ[1] = p ≫ SSet.ι₁ := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, H.h₁, SSet.comp_const]
  let r := simplicialPointFiberLift p b f hf
  have hr : F.ι ≫ r = 𝟙 _ := by
    apply (cancel_mono F.ι).mp
    rw [Category.assoc, simplicialPointFiberLift_ι, Category.id_comp]
    dsimp only [f]
    have hn : F.ι ≫ SSet.ι₁ = SSet.ι₁ ≫ F.ι ▷ Δ[1] := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, hei]
    rfl
  refine ⟨r, hr, ⟨{ h := e, h₀ := he₀, h₁ := ?_, rel := ?_ }, hei, hep⟩⟩
  · exact (simplicialPointFiberLift_ι p b f hf).symm
  · apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- A stationary simplicial deformation gives the actual weak-equivalence
statement on realization, without a Kan–Quillen input. -/
theorem simplicial_retraction_weak {A E : SSet.{0}} (i : A ⟶ E) (r : E ⟶ A)
    (hir : i ≫ r = 𝟙 A) (H : SSet.Homotopy (𝟙 E) (r ≫ i)) :
    realizationWeakEquivalences i := by
  apply homotopyEquiv_isWeakHomotopyEquivalence
    (show ContinuousMap.HomotopyEquiv (SSet.toTop.obj A) (SSet.toTop.obj E) from {
      toFun := (SSet.toTop.map i).hom
      invFun := (SSet.toTop.map r).hom
      left_inv := by
        have he := SSet.toTop.congr_map hir
        rw [SSet.toTop.map_comp, SSet.toTop.map_id] at he
        have he' := congrArg TopCat.Hom.hom he
        change (SSet.toTop.map r).hom.comp (SSet.toTop.map i).hom =
          ContinuousMap.id _ at he'
        rw [he']
      right_inv := by
        have h := (RealizedCylinder.homotopy H).symm
        exact ⟨{ toContinuousMap := h.toContinuousMap
                 map_zero_left := fun x => by
                   change h (0, x) = (SSet.toTop.map i).hom ((SSet.toTop.map r).hom x)
                   exact (h.apply_zero x).trans
                     (congrArg (fun q => q.hom x) (SSet.toTop.map_comp r i))
                 map_one_left := fun x => by
                   change h (1, x) = x
                   exact (h.apply_one x).trans
                     (congrArg (fun q => q.hom x) (SSet.toTop.map_id E)) }⟩ })

end

end Thomason.Construction

end

section

/-! # Kan horn filling in literal simplicial vertex fibres -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A literal vertex fibre of any Kan fibration is a Kan complex. The horn
filler has constant projection, so it lies in the same fibre in all degrees. -/
theorem simplicialPointFiber_kan {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (b : B _⦋0⦌) :
    SSet.KanComplex (simplicialPointFiber p b).toSSet := by
  apply SSet.KanComplex.iff.mpr
  intro n j f hf
  let a := hf.desc ≫ (simplicialPointFiber p b).ι
  have ha : a ≫ p = SSet.const b := by
    dsimp only [a]
    rw [Category.assoc, simplicialPointFiber_ι_comp, SSet.comp_const]
  obtain ⟨l, hl, hp⟩ := (SSet.horn.IsCompatible.of_hom a).exists_lift p
    (SSet.const b) (fun k hk => by
      rw [Category.assoc, ha, SSet.comp_const, SSet.comp_const])
  let q := simplicialPointFiberLift p b l hp
  refine ⟨q, ?_⟩
  intro k hk
  apply (cancel_mono (simplicialPointFiber p b).ι).mp
  rw [Category.assoc, simplicialPointFiberLift_ι, hl k hk]
  dsimp only [a]
  rw [← Category.assoc, SSet.horn.IsCompatible.ι_desc]

end

end Thomason.Construction

end

section

/-! # Relative uniqueness of lifts across an anodyne inclusion -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Two lifts that agree on an anodyne subobject have a simplicial homotopy
over the same base map, stationary on that entire subobject. -/
theorem kan_lifts_homotopic_relative {A K E B : SSet.{0}} (i : A ⟶ K)
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f g : K ⟶ E) (hfg : f ≫ p = g ≫ p) (hA : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst K Δ[1] ≫ f ≫ p ∧
      i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ i ≫ f := by
  let a : A ⊗ Δ[1] ⟶ E := fst A Δ[1] ≫ i ≫ f
  let b : K ⊗ Δ[1] ⟶ B := fst K Δ[1] ≫ f ≫ p
  let c := intervalBoundaryFamily f g
  have hc : i ▷ (SSet.boundary 1 : SSet.{0}) ≫ c = A ◁ (SSet.boundary 1).ι ≫ a := by
    dsimp only [c]
    rw [intervalBoundaryFamily_naturality, ← hA, intervalBoundaryFamily_restriction]
    dsimp only [a]
    simp only [← Category.assoc, SSet.ι₀_fst, SSet.ι₁_fst, Category.id_comp]
  have ha : a ≫ p = i ▷ Δ[1] ≫ b := by
    dsimp only [a, b]
    rw [← Category.assoc (i ▷ Δ[1]), whiskerRight_fst]
    simp only [Category.assoc]
  have hb : c ≫ p = K ◁ (SSet.boundary 1).ι ≫ b := by
    apply interval_boundary_tensor_hom_ext
    · dsimp only [c, b]
      rw [← Category.assoc, intervalBoundaryFamily_zero,
        ← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι, whisker_zero_face]
      simp only [Category.assoc, ← Category.assoc SSet.ι₀, SSet.ι₀_fst, Category.id_comp]
    · dsimp only [c, b]
      rw [← Category.assoc, intervalBoundaryFamily_one,
        ← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι, whisker_one_face]
      simp only [Category.assoc, ← Category.assoc SSet.ι₁, SSet.ι₁_fst, Category.id_comp]
      rw [hfg]
  obtain ⟨e, heA, heC, hep⟩ := exists_kan_boundary_cylinder_lift i hi p a c b hc ha hb
  obtain ⟨he₀, he₁⟩ := intervalBoundaryFamily_endpoints e f g heC
  let H : SSet.Homotopy f g := {
    h := e
    h₀ := he₀
    h₁ := he₁
    rel := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  exact ⟨H, hep, heA⟩

/-- Projection of a product with a Kan complex is a Kan fibration. -/
theorem kan_product_snd_fibration (F B : SSet.{0}) [SSet.KanComplex F] :
    HomotopicalAlgebra.Fibration (snd F B) := by
  rw [fibration_iff]
  intro A K i hi
  have : HasLiftingProperty i (terminal.from F) :=
    ((fibration_iff (terminal.from F)).mp inferInstance) _ hi
  refine ⟨fun {a b} sq => ?_⟩
  let s : CommSq (a ≫ fst F B) i (terminal.from F) (terminal.from K) :=
    ⟨terminal.hom_ext _ _⟩
  refine ⟨⟨{ l := lift s.lift b, fac_left := ?_, fac_right := lift_snd _ _ }⟩⟩
  apply hom_ext
  · rw [Category.assoc, lift_fst, s.fac_left]
  · rw [Category.assoc, lift_snd, sq.w]

end

end Thomason.Construction

end

section

/-! # Endpoints and stationarity of the actual poset cone realization -/

namespace Thomason.Construction.ConePrism

open CategoryTheory CategoryTheory.Limits Convexity

/-- The zero endpoint of the barycentric cone is the original last face. -/
theorem liftedBarycentric_zero (n : ℕ) :
    TopologicalInterval.sectionAt (SimplexCategory.toTop.{0}.obj (.mk n)) 0 ≫
      liftedBarycentric n =
    SimplexCategory.toTop.{0}.map (SimplexCategory.Hom.mk Fin.castSuccOrderEmb.toOrderHom) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrArg ULift.up (barycentric_zero n x.down)

variable {P : Type} [PartialOrder P] (v : P) (hv : ∀ x, x ≤ v)

/-- The actual point of the realization represented by the greatest vertex. -/
noncomputable def vertexPoint : SSet.toTop.obj (nerve P) :=
  (RealizationPrism.leg (nerve P) (vertexIndex v)).hom (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1)))

/-- Every original simplex is recovered at the zero endpoint. -/
theorem piece_zero (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    TopologicalInterval.sectionAt ((RealizationPrism.diagram (nerve P)).obj j) 0 ≫
      piece v hv j = RealizationPrism.leg (nerve P) j := by
  change TopologicalInterval.sectionAt (SimplexCategory.toTop.obj j.left) 0 ≫
    (liftedBarycentric j.left.len ≫ RealizationPrism.leg (nerve P) (coneIndex v hv j)) = _
  rw [← Category.assoc, liftedBarycentric_zero]
  exact (RealizationPrism.cocone (nerve P)).w (faceMap v hv j)

/-- The new final vertex of each cone represents the chosen realization point. -/
theorem leg_final_vertex (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    (RealizationPrism.leg (nerve P) (coneIndex v hv j)).hom
      (ULift.up (.single (Fin.last (j.left.len+1)))) = vertexPoint v := by
  have he := congrArg (fun f => f.hom (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1))))
    ((RealizationPrism.cocone (nerve P)).w (vertexMap v hv j))
  change (RealizationPrism.leg (nerve P) (coneIndex v hv j)).hom
    (ULift.up (StdSimplex.map (fun _ : Fin 1 => Fin.last (j.left.len+1))
      (StdSimplex.single (R := ℝ) (0 : Fin 1)))) = vertexPoint v at he
  simpa only [StdSimplex.map_single] using he

/-- Every cone piece reaches the same point at the one endpoint. -/
theorem piece_one (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    TopologicalInterval.sectionAt ((RealizationPrism.diagram (nerve P)).obj j) 1 ≫
      piece v hv j = TopCat.ofHom (ContinuousMap.const _ (vertexPoint v)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (RealizationPrism.leg (nerve P) (coneIndex v hv j)).hom
    (ULift.up (barycentric j.left.len (x.down, 1))) = vertexPoint v
  rw [barycentric_one]
  exact leg_final_vertex v hv j

/-- The entire cone simplex on the greatest vertex is constant in realization. -/
theorem leg_cone_vertex_constant
    (x : SimplexCategory.toTop.{0}.obj (.mk 1)) :
    (RealizationPrism.leg (nerve P) (coneIndex v hv (vertexIndex v))).hom x = vertexPoint v := by
  have he := congrArg (fun f => f.hom x)
    ((RealizationPrism.cocone (nerve P)).w (collapseVertex v hv))
  exact he.symm.trans (congrArg (RealizationPrism.leg (nerve P) (vertexIndex v)).hom
    (Subsingleton.elim _ (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1)))))

/-- The assembled actual cone is stationary on its greatest vertex. -/
theorem realizationCone_vertex (t : unitInterval) :
    (realizationCone v hv).hom (vertexPoint v, t) = vertexPoint v := by
  have he := congrArg (fun f => f.hom (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1)), t))
    (RealizationPrism.assemble_fac (nerve P) _ (piece v hv) (piece_naturality v hv)
      (vertexIndex v))
  exact he.trans (leg_cone_vertex_constant v hv _)

end Thomason.Construction.ConePrism

end

section

/-! # Greatest-vertex weak equivalences without Kan–Quillen

The explicit cone prisms give a topological strong deformation retraction
of the realization of an ordinary poset nerve onto its greatest vertex.
-/

namespace Thomason.Construction.ConePrism

open CategoryTheory CategoryTheory.Limits Convexity

variable {P : Type} [PartialOrder P] (v : P) (hv : ∀ x, x ≤ v)

/-- The realization of the zero-simplex map is the constant map to its vertex. -/
theorem realized_vertex_constant (x : SSet.toTop.obj (SSet.stdSimplex.obj (.mk 0))) :
    (SSet.toTop.map (vertexIndex v).hom).hom x = vertexPoint v := by
  let : Unique (SSet.toTop.obj (SSet.stdSimplex.obj (.mk 0))) :=
    (TopCat.homeoOfIso (SSet.toTopSimplex.app (.mk 0))).toEquiv.unique
  have hx : x = (SSet.toTopSimplex.inv.app (.mk 0)).hom
      (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1))) := Subsingleton.elim _ _
  exact congrArg (SSet.toTop.map (vertexIndex v).hom).hom hx

/-- The actual continuous homotopy from identity to the greatest vertex. -/
noncomputable def contraction :
    (ContinuousMap.id (SSet.toTop.obj (nerve P))).Homotopy
      (ContinuousMap.const _ (vertexPoint v)) :=
  RealizationPrism.homotopy (nerve P) _ (piece v hv) (piece_naturality v hv)
    (𝟙 _) (TopCat.ofHom (ContinuousMap.const _ (vertexPoint v)))
    (fun j => (piece_zero v hv j).trans (Category.comp_id _).symm)
    (fun j => (piece_one v hv j).trans rfl)

include hv

/-- The actual simplicial inclusion of the greatest vertex is a realization
weak equivalence. No model structure or KQ input is used. -/
theorem greatest_vertex_weak : realizationWeakEquivalences (vertexIndex v).hom := by
  let i := SSet.toTop.map (vertexIndex v).hom
  let r₀ := SSet.stdSimplex.isTerminalObj₀.from (nerve P)
  let r := SSet.toTop.map r₀
  have hir : i ≫ r = 𝟙 _ := by
    change SSet.toTop.map (vertexIndex v).hom ≫ SSet.toTop.map r₀ = _
    rw [← SSet.toTop.map_comp]
    have h : (vertexIndex v).hom ≫ r₀ = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
    exact SSet.toTop.map_id _
  have hc : i.hom.comp r.hom = ContinuousMap.const _ (vertexPoint v) := by
    apply ContinuousMap.ext
    intro x
    exact realized_vertex_constant v (r.hom x)
  let H : (ContinuousMap.const (SSet.toTop.obj (nerve P)) (vertexPoint v)).HomotopyRel
      (ContinuousMap.id _) (Set.range i.hom) := {
    toHomotopy := (contraction v hv).symm
    prop' := by
      intro t z hz
      obtain ⟨x, rfl⟩ := hz
      change (realizationCone v hv).hom (i.hom x, unitInterval.symm t) = vertexPoint v
      rw [realized_vertex_constant v x]
      exact realizationCone_vertex v hv _ }
  exact weakEquivalence_of_strongDeformationRetract i.hom r.hom
    (congrArg TopCat.Hom.hom hir) (H.cast hc.symm rfl)

end Thomason.Construction.ConePrism

end

section

/-! # The actual quotient topology of geometric realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Topology

noncomputable section

/-- Openness in realization is tested on all of its actual simplex maps. -/
theorem isOpen_iff_simplex (K : SSet.{0}) (U : Set (SSet.toTop.obj K)) :
    IsOpen U ↔ ∀ j, IsOpen ((leg K j).hom ⁻¹' U) :=
  TopCat.isOpen_iff_of_isColimit (cocone K) (isColimit K) U

/-- Closedness in realization has the same simplexwise test. -/
theorem isClosed_iff_simplex (K : SSet.{0}) (A : Set (SSet.toTop.obj K)) :
    IsClosed A ↔ ∀ j, IsClosed ((leg K j).hom ⁻¹' A) :=
  TopCat.isClosed_iff_of_isColimit (cocone K) (isColimit K) A

/-- The final topology detects continuity of any proposed map out of realization. -/
theorem continuous_iff_simplex (K : SSet.{0}) {Y : Type*} [TopologicalSpace Y]
    (f : SSet.toTop.obj K → Y) :
    Continuous f ↔ ∀ j, Continuous (f ∘ (leg K j).hom) :=
  TopCat.continuous_iff_of_isColimit (cocone K) (isColimit K) f

/-- The disjoint union of all simplex parameter spaces, with their given topologies. -/
abbrev SimplexPoints (K : SSet.{0}) :=
  Σ j : CostructuredArrow SSet.stdSimplex K, (diagram K).obj j

/-- The canonical map from simplex representatives onto realization. -/
def quotientProjection (K : SSet.{0}) : SimplexPoints K → SSet.toTop.obj K :=
  fun p => (leg K p.1).hom p.2

theorem quotientProjection_surjective (K : SSet.{0}) :
    Function.Surjective (quotientProjection K) := by
  intro x
  obtain ⟨j, p, hp⟩ := point_representation K x
  exact ⟨⟨j, p⟩, hp⟩

/-- Geometric realization carries exactly the quotient topology of simplex representatives. -/
theorem quotientProjection_isQuotientMap (K : SSet.{0}) :
    IsQuotientMap (quotientProjection K) := by
  rw [isQuotientMap_iff]
  refine ⟨?_, quotientProjection_surjective K⟩
  apply IsCoinducing.of_isOpen_preimage_iff_isOpen
  intro U
  rw [isOpen_iff_simplex, isOpen_sigma_iff]
  rfl

end

end Thomason.Construction.RealizationPrism

end

end OAI
