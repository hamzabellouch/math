import OAI.GroupTheory.Thompson.DyadicGapChain
import OAI.GroupTheory.Thompson.DyadicArithmetic
import OAI.GroupTheory.Thompson.SortedSubdivision
import Mathlib.Order.Fin.Basic

namespace OAI

/-!
# Indexed knots of an ordered dyadic chain

An actual consecutive list of dyadic cells covering `[0,1]` gives a strictly
increasing subdivision indexed by that same list. The two endpoints of its
`i`th piece are exactly the endpoints of the `i`th listed cell.
-/

noncomputable section

namespace ThompsonNonamenability

namespace GapChain

/-- The initial endpoint followed by the right endpoints of the cells. -/
def realKnots : (a : ℝ) → (L : List BasicInterval) → Fin (L.length + 1) → ℝ
  | a, [], _ => a
  | a, I :: L, i => Fin.cases a (realKnots I.right L) i

@[simp] theorem realKnots_zero (a : ℝ) (L : List BasicInterval) :
    realKnots a L 0 = a := by
  cases L <;> rfl

/-- The right knot of each indexed piece is its actual right endpoint. -/
theorem realKnots_succ (a : ℝ) (L : List BasicInterval) (i : Fin L.length) :
    realKnots a L i.succ = (L.get i).right := by
  induction L generalizing a with
  | nil => exact Fin.elim0 i
  | cons I L ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change realKnots I.right L 0 = I.right
        exact realKnots_zero I.right L
      · change realKnots I.right L j.succ = (L.get j).right
        exact ih I.right j

/-- The chain equalities identify each left knot with its listed cell. -/
theorem realKnots_castSucc {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (i : Fin L.length) :
    realKnots a L i.castSucc = (L.get i).left := by
  induction L generalizing a with
  | nil => exact Fin.elim0 i
  | cons I L ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change a = I.left
        exact h.1.symm
      · change realKnots I.right L j.castSucc = (L.get j).left
        exact ih h.2 j

theorem realKnots_last {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : realKnots a L (Fin.last L.length) = b := by
  induction L generalizing a with
  | nil => exact h
  | cons I L ih =>
      change realKnots I.right L (Fin.last L.length) = b
      exact ih h.2

theorem strictMono_realKnots {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : StrictMono (realKnots a L) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [realKnots_castSucc h i, realKnots_succ]
  exact (L.get i).left_lt_right

theorem length_pos {L : List BasicInterval} (h : GapChain 0 1 L) :
    0 < L.length := by
  cases L with
  | nil => exact False.elim (zero_ne_one h)
  | cons I L => exact Nat.zero_lt_succ _

theorem realKnots_mem_unit {L : List BasicInterval} (h : GapChain 0 1 L)
    (i : Fin (L.length + 1)) : realKnots 0 L i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hi := h.strictMono_realKnots.monotone (Fin.zero_le i)
    simpa only [realKnots_zero] using hi
  · have hi := h.strictMono_realKnots.monotone (Fin.le_last i)
    simpa only [realKnots_last h] using hi

theorem isDyadic_realKnots (L : List BasicInterval) (i : Fin (L.length + 1)) :
    IsDyadic (realKnots 0 L i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [realKnots_zero] using isDyadic_zero
  · rw [realKnots_succ]
    refine ⟨((L.get j).index.val : ℤ) + 1, (L.get j).depth, ?_⟩
    simp only [BasicInterval.right, Int.cast_add, Int.cast_natCast, Int.cast_one]

end GapChain

/-- A subdivision whose indexing agrees with an actual ordered cell list. -/
structure ChainSubdivision (L : List BasicInterval) where
  positive : 0 < L.length
  knots : Fin (L.length + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last L.length) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin L.length,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  left_eq : ∀ i : Fin L.length, (knots i.castSucc : ℝ) = (L.get i).left
  right_eq : ∀ i : Fin L.length, (knots i.succ : ℝ) = (L.get i).right

namespace GapChain

/-- Construct all subdivision data from the chain equalities. -/
def toSubdivision {L : List BasicInterval} (h : GapChain 0 1 L) :
    ChainSubdivision L := by
  let knots : Fin (L.length + 1) → UnitInterval :=
    fun i => ⟨realKnots 0 L i, h.realKnots_mem_unit i⟩
  have hfirst : knots 0 = unitIntervalZero := by
    apply Subtype.ext
    exact realKnots_zero 0 L
  have hlast : knots (Fin.last L.length) = unitIntervalOne := by
    apply Subtype.ext
    exact realKnots_last h
  exact
    { positive := h.length_pos
      knots := knots
      strictMono_knots := fun _ _ hij => h.strictMono_realKnots hij
      first := hfirst
      last := hlast
      dyadic := isDyadic_realKnots L
      cover := SortedSubdivision.cover_of_endpoints h.length_pos knots hfirst hlast
      left_eq := realKnots_castSucc h
      right_eq := realKnots_succ 0 L }

end GapChain

namespace ChainSubdivision

/-- Membership in an indexed cell is exactly membership between its knots. -/
theorem mem_carrier_iff {L : List BasicInterval} (s : ChainSubdivision L)
    (i : Fin L.length) (x : UnitInterval) :
    (x : ℝ) ∈ (L.get i).carrier ↔ s.knots i.castSucc ≤ x ∧ x ≤ s.knots i.succ := by
  change (L.get i).left ≤ (x : ℝ) ∧ (x : ℝ) ≤ (L.get i).right ↔ _
  rw [← s.left_eq i, ← s.right_eq i]
  rfl

end ChainSubdivision

end ThompsonNonamenability

end

end OAI
