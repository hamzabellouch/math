import Mathlib.Data.Fintype.Prod
import OAI.AlgebraicGeometry.PlaneCurves.LineObstructions

namespace OAI

/-!
# Transverse projective line arrangements; Extension of finite tuples by additional distinct points
-/

section

/-!
# Concrete reduced line arrangement for the alternative square-case argument
-/
noncomputable section
namespace Nagata.W06.LineArrangement
open scoped BigOperators

/-- Positive x-coordinate of mark s, where U=-x. The first mark of line zero
is moved from 1 to k+1; every other first mark remains 1. -/
def markedCoordinate (k i : ℕ) (s : Fin k) : ℕ :=
  if s.val = 0 then Nagata.W04.ReducibleSquare.firstMark k i else s.val + 1

theorem markedCoordinate_pos (k i : ℕ) (s : Fin k) : 0 < markedCoordinate k i s := by
  unfold markedCoordinate
  split_ifs
  · exact Nagata.W04.ReducibleSquare.firstMark_pos k i
  · omega

theorem markedCoordinate_zero (k i : ℕ) (hk : 0 < k) :
    markedCoordinate k i ⟨0, hk⟩ = Nagata.W04.ReducibleSquare.firstMark k i := by
  simp [markedCoordinate]

theorem markedCoordinate_of_ne_zero (k i : ℕ) (s : Fin k) (hs : s.val ≠ 0) :
    markedCoordinate k i s = s.val + 1 := by
  simp [markedCoordinate, hs]

theorem markedCoordinate_injective (k i : ℕ) :
    Function.Injective (markedCoordinate k i) := by
  intro s t h
  apply Fin.ext
  dsimp [markedCoordinate, Nagata.W04.ReducibleSquare.firstMark] at h
  split_ifs at h <;> omega

variable {K : Type*} [Field K]

/-- Affine graph of line i in the U-coordinate. -/
def graphValue (i : ℕ) (U : K) : K := (i : K) ^ 2 - (i : K) * U

/-- The actual affine line equation evaluated at a point. -/
def lineValue (i : ℕ) (U Y : K) : K := Y - graphValue i U

/-- The pairwise node of components i and j. -/
def node (i j : ℕ) : K × K := ((i : K) + (j : K), -(i : K) * (j : K))

/-- The k marked points of component i, in actual affine coordinates (U,Y). -/
def markedPoint (K : Type*) [Field K] (k : ℕ) (i s : Fin k) : K × K :=
  let U : K := -(markedCoordinate k i.val s : K)
  (U, graphValue i.val U)

theorem graphValue_sub (i j : ℕ) (U : K) :
    graphValue i U - graphValue j U =
      ((i : K) - (j : K)) * ((i : K) + (j : K) - U) := by
  unfold graphValue
  ring

theorem graphValue_at_node (i j : ℕ) :
    graphValue i ((i : K) + (j : K)) = -(i : K) * (j : K) := by
  unfold graphValue
  ring

theorem node_on_left (i j : ℕ) : lineValue i (node (K := K) i j).1 (node (K := K) i j).2 = 0 := by
  simp [node, lineValue, graphValue_at_node]

theorem node_on_right (i j : ℕ) : lineValue j (node (K := K) i j).1 (node (K := K) i j).2 = 0 := by
  unfold node lineValue graphValue
  ring

theorem lineValue_at_node (i j l : ℕ) :
    lineValue l (node (K := K) i j).1 (node (K := K) i j).2 =
      -(((l : K) - (i : K)) * ((l : K) - (j : K))) := by
  unfold node lineValue graphValue
  ring

variable [CharZero K]

/-- Distinct component graphs meet at precisely the explicitly specified node. -/
theorem intersection_iff_node (i j : ℕ) (hij : i ≠ j) (p : K × K) :
    (lineValue i p.1 p.2 = 0 ∧ lineValue j p.1 p.2 = 0) ↔ p = node i j := by
  constructor
  · rintro ⟨hi, hj⟩
    have hi' : p.2 = graphValue i p.1 := sub_eq_zero.mp hi
    have hj' : p.2 = graphValue j p.1 := sub_eq_zero.mp hj
    have hprod : ((i : K) - (j : K)) * ((i : K) + (j : K) - p.1) = 0 := by
      rw [← graphValue_sub, sub_eq_zero]
      exact hi'.symm.trans hj'
    have hne : (i : K) - (j : K) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
    have hU : p.1 = (i : K) + (j : K) :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)).symm
    apply Prod.ext hU
    rw [hi', hU, graphValue_at_node]
    rfl
  · intro hp
    subst p
    exact ⟨node_on_left i j, node_on_right i j⟩

/-- No third distinct component passes through a pairwise node. -/
theorem node_avoids_third (i j l : ℕ) (hli : l ≠ i) (hlj : l ≠ j) :
    lineValue l (node (K := K) i j).1 (node (K := K) i j).2 ≠ 0 := by
  rw [lineValue_at_node]
  apply neg_ne_zero.mpr
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast hli)
  · exact sub_ne_zero.mpr (by exact_mod_cast hlj)

theorem no_triple_concurrence (i j l : ℕ) (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (p : K × K) (hi : lineValue i p.1 p.2 = 0) (hj : lineValue j p.1 p.2 = 0) :
    lineValue l p.1 p.2 ≠ 0 := by
  rw [(intersection_iff_node i j hij p).mp ⟨hi, hj⟩]
  exact node_avoids_third i j l hli hlj

/-- Every negative-U mark on one component avoids every other component. -/
theorem negative_mark_avoids_other_line (i j v : ℕ) (hij : i ≠ j) (hv : 0 < v) :
    lineValue j (-(v : K)) (graphValue i (-(v : K))) ≠ 0 := by
  unfold lineValue
  rw [graphValue_sub, sub_neg_eq_add]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast hij)
  · exact_mod_cast (show i + j + v ≠ 0 by omega)

omit [CharZero K] in
theorem markedPoint_on_line (k : ℕ) (i s : Fin k) :
    lineValue i.val (markedPoint K k i s).1 (markedPoint K k i s).2 = 0 := by
  simp [markedPoint, lineValue]

theorem markedPoint_avoids_other_line (k : ℕ) (i j s : Fin k) (hij : i ≠ j) :
    lineValue j.val (markedPoint K k i s).1 (markedPoint K k i s).2 ≠ 0 := by
  exact negative_mark_avoids_other_line i.val j.val (markedCoordinate k i.val s)
    (fun h => hij (Fin.ext h)) (markedCoordinate_pos k i.val s)

/-- All k² displayed marked affine points are pairwise distinct. -/
theorem markedPoint_injective (k : ℕ) :
    Function.Injective (fun p : Fin k × Fin k => markedPoint K k p.1 p.2) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  dsimp only at h
  have hij : i = j := by
    by_contra hij
    have hn := markedPoint_avoids_other_line (K := K) k i j s hij
    apply hn
    rw [h]
    exact markedPoint_on_line k j t
  apply Prod.ext hij
  have hU := congrArg Prod.fst h
  have hcoord : markedCoordinate k i.val s = markedCoordinate k j.val t := by
    exact Nat.cast_injective (neg_injective hU)
  rw [hij] at hcoord
  exact markedCoordinate_injective k j.val hcoord

/-- The actual finite set of marked affine points. -/
def markedPoints (K : Type*) [Field K] (k : ℕ) : Finset (K × K) := by
  classical
  exact Finset.univ.image (fun p : Fin k × Fin k => markedPoint K k p.1 p.2)

theorem card_markedPoints (k : ℕ) : (markedPoints K k).card = k ^ 2 := by
  classical
  unfold markedPoints
  rw [Finset.card_image_of_injective _ (markedPoint_injective k)]
  simp [pow_two]

/-- The affine component sets are genuinely distinct, witnessed by U=-1. -/
theorem line_sets_injective :
    Function.Injective (fun i : ℕ => {p : K × K | lineValue i p.1 p.2 = 0}) := by
  intro i j h
  dsimp only at h
  by_contra hij
  have hi : ((-1 : K), graphValue i (-1 : K)) ∈ {p : K × K | lineValue i p.1 p.2 = 0} := by
    simp [lineValue]
  rw [h] at hi
  exact negative_mark_avoids_other_line i j 1 hij (by norm_num) (by simpa using hi)

end Nagata.W06.LineArrangement

end
end

section

/-! One additional affine point on component zero, outside all k² marks and nodes. -/
noncomputable section
namespace Nagata.W06.LineArrangement

/-- Every marked positive x-coordinate is at most k+1. -/
theorem markedCoordinate_le_succ (k i : ℕ) (s : Fin k) :
    markedCoordinate k i s ≤ k + 1 := by
  unfold markedCoordinate Nagata.W04.ReducibleSquare.firstMark
  split_ifs <;> omega

/-- The extra point on line zero. For the triangle it is (-5,0). -/
def additionalPoint (K : Type*) [Field K] (k : ℕ) : K × K :=
  (-((k + 2 : ℕ) : K), 0)

variable {K : Type*} [Field K] [CharZero K]

/-- The extra point differs from every one of the original k² marks. -/
theorem additionalPoint_ne_mark (k : ℕ) (i s : Fin k) :
    additionalPoint K k ≠ markedPoint K k i s := by
  intro h
  have hU := congrArg Prod.fst h
  have hn : k + 2 = markedCoordinate k i.val s :=
    Nat.cast_injective (neg_injective hU)
  have hb := markedCoordinate_le_succ k i.val s
  omega

theorem additionalPoint_not_mem_markedPoints (k : ℕ) :
    additionalPoint K k ∉ markedPoints K k := by
  classical
  intro h
  obtain ⟨⟨i, s⟩, _, hp⟩ := Finset.mem_image.mp h
  exact additionalPoint_ne_mark k i s hp.symm

omit [CharZero K] in
theorem additionalPoint_on_zero (k : ℕ) :
    lineValue 0 (additionalPoint K k).1 (additionalPoint K k).2 = 0 := by
  simp [additionalPoint, lineValue, graphValue]

/-- The extra point lies on no component other than component zero. -/
theorem additionalPoint_avoids_other_line (k j : ℕ) (hj : j ≠ 0) :
    lineValue j (additionalPoint K k).1 (additionalPoint K k).2 ≠ 0 := by
  simpa [additionalPoint, graphValue] using
    negative_mark_avoids_other_line (K := K) 0 j (k + 2) (Ne.symm hj) (by omega)

/-- Its negative U-coordinate prevents coincidence with any positive pairwise node. -/
theorem additionalPoint_ne_node (k i j : ℕ) :
    additionalPoint K k ≠ node (K := K) i j := by
  intro h
  have hU := congrArg Prod.fst h
  change -((k + 2 : ℕ) : K) = (i : K) + (j : K) at hU
  have hz' : ((k + 2 : ℕ) : K) + ((i : K) + (j : K)) = 0 := by
    rw [← hU, add_neg_cancel]
  have hz : (((k + 2) + i + j : ℕ) : K) = 0 := by
    simpa only [Nat.cast_add, add_assoc] using hz' 
  have hn : (k + 2) + i + j = 0 := Nat.cast_eq_zero.mp hz
  omega

/-- The concrete original marks together with the one extra point. -/
def extendedMarkedPoints (K : Type*) [Field K] (k : ℕ) : Finset (K × K) := by
  classical
  exact insert (additionalPoint K k) (markedPoints K k)

/-- The explicit extra point increases the cardinality to k²+1. -/
theorem card_insert_additionalPoint (k : ℕ) :
    (extendedMarkedPoints K k).card = k ^ 2 + 1 := by
  classical
  unfold extendedMarkedPoints
  rw [Finset.card_insert_of_notMem (additionalPoint_not_mem_markedPoints k), card_markedPoints]

end Nagata.W06.LineArrangement

end
end

end OAI
