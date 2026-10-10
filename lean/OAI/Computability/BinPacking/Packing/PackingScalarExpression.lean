import OAI.Computability.BinPacking.Arithmetic.NatExpression
import OAI.Computability.BinPacking.Inventory.InventoryPrefixConservation

namespace OAI

namespace BinPackingGap.InventoryData

open IntegerPackingArithmetic

variable (D : InventoryData)

def coordinateDenominator : ℕ :=
  geomDenominator D.graph.edges.length D.R D.geometryBound D.L

theorem coordinateDenominator_pos : 0 < D.coordinateDenominator :=
  geomDenominator_pos _ _ _ _

def treeBaselineInteger : D.TreeRow → ℤ
  | .inl (node, _) =>
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
  | .inr (.inl (node, _)) =>
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
  | .inr (.inr _) => D.coordinateDenominator

def rowBaselineInteger {v : D.Vertex} : D.RowAt v → ℤ
  | .inl r => D.treeBaselineInteger r
  | .inr (_, j) => baselineNumerator D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)

def treeDeadlineInteger : D.TreeRow → ℤ
  | .inl (node, _) =>
      if node.val ∈ D.plus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
  | .inr (.inl (node, _)) =>
      if node.val ∈ D.minus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
  | .inr (.inr _) => D.coordinateDenominator

def deadlineInteger {v : D.Vertex} : D.MBase v → ℤ
  | .inl r => D.treeDeadlineInteger r
  | .inr j => baselineNumerator D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j) - 1

def rowIntegerCoordinate {v : D.Vertex} (r : D.RowAt v) : ℤ :=
  D.rowBaselineInteger r - if D.rowShort r then 1 else 0

def anchorIntegerCoordinate {v : D.Vertex} : D.AnchorAt v → ℤ
  | .inl z => -D.deadlineInteger z
  | .inr j =>
      -baselineNumerator D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j) -
        betaNumerator D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j).1

def globalIntegerCoordinate : D.GlobalCopy → ℤ
  | ⟨.up one, _⟩ => -(if one then (D.coordinateDenominator : ℤ) else 0)
  | ⟨.um one, _⟩ => -(if one then (D.coordinateDenominator : ℤ) else 0)
  | ⟨.edge e permit, _⟩ =>
      betaNumerator D.graph.edges.length D.R D.geometryBound D.L e +
        if permit then 0 else 1

def localIntegerCoordinate {v : D.Vertex} : D.LocalAt v → ℤ
  | .inl (.inl ⟨ell, _⟩) => -(localNumerator D.geometryBound D.L ell.val : ℤ)
  | _ => 0

def itemIntegerCoordinate : D.Item → ℤ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowIntegerCoordinate r
  | ⟨.anchor, ⟨_, a⟩⟩ => D.anchorIntegerCoordinate a
  | ⟨.«global», u⟩ => D.globalIntegerCoordinate u
  | ⟨.«local», ⟨_, l⟩⟩ => D.localIntegerCoordinate l
  | ⟨.flag, _⟩ => 0

variable (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L)

include hplus hminus in
theorem coordinateDenominator_mul_treeBaseline (r : D.TreeRow) :
    (D.coordinateDenominator : ℚ) * D.treeBaseline r =
      (D.treeBaselineInteger r : ℚ) := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · simpa only [treeBaseline, treeBaselineInteger, Int.cast_natCast,
      coordinateDenominator] using
      geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
        .plus node.val ((D.plus.length_le_height node.property).trans hplus)
  · simpa only [treeBaseline, treeBaselineInteger, Int.cast_natCast,
      coordinateDenominator] using
      geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
        .minus node.val ((D.minus.length_le_height node.property).trans hminus)
  · simp [treeBaseline, treeBaselineInteger]

include hplus hminus in
theorem coordinateDenominator_mul_rowBaseline {v : D.Vertex} (r : D.RowAt v) :
    (D.coordinateDenominator : ℚ) * D.rowBaseline r =
      (D.rowBaselineInteger r : ℚ) := by
  rcases r with r | ⟨b, j⟩
  · exact D.coordinateDenominator_mul_treeBaseline hplus hminus r
  · exact geomDenominator_mul_baseline _ _ _ _ _

include hplus hminus in
theorem coordinateDenominator_mul_treeDeadline (r : D.TreeRow) :
    (D.coordinateDenominator : ℚ) * D.treeDeadline r =
      (D.treeDeadlineInteger r : ℚ) := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · have hn := (D.plus.length_le_height node.property).trans hplus
    by_cases hl : node.val ∈ D.plus.leaves
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_true, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeLeft D.graph.edges.length D.R D.geometryBound D.L
          .plus node.val hn
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_false, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
          .plus node.val hn
  · have hn := (D.minus.length_le_height node.property).trans hminus
    by_cases hl : node.val ∈ D.minus.leaves
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_true, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeLeft D.graph.edges.length D.R D.geometryBound D.L
          .minus node.val hn
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_false, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
          .minus node.val hn
  · simp [treeDeadline, treeDeadlineInteger]

include hplus hminus in
theorem coordinateDenominator_mul_deadline {v : D.Vertex} (r : D.MBase v) :
    (D.coordinateDenominator : ℚ) * D.deadline r =
      (D.deadlineInteger r : ℚ) := by
  rcases r with r | j
  · exact D.coordinateDenominator_mul_treeDeadline hplus hminus r
  · simp only [deadline, deadlineInteger, Geometry.jobLeft, mul_sub, Int.cast_sub,
      Int.cast_one, coordinateDenominator, geomDenominator_mul_baseline,
      geomDenominator_mul_delta]

include hplus hminus in
theorem coordinateDenominator_mul_rowCoordinate {v : D.Vertex} (r : D.RowAt v) :
    (D.coordinateDenominator : ℚ) * D.rowCoordinate r =
      (D.rowIntegerCoordinate r : ℚ) := by
  have hb := D.coordinateDenominator_mul_rowBaseline hplus hminus r
  simp only [coordinateDenominator] at hb
  have hd := geomDenominator_mul_delta D.graph.edges.length D.R D.geometryBound D.L
  cases hs : D.rowShort r <;>
    simp [rowCoordinate, rowIntegerCoordinate, hs, mul_sub, hb,
      coordinateDenominator, hd]

include hplus hminus in
theorem coordinateDenominator_mul_anchorCoordinate {v : D.Vertex} (r : D.AnchorAt v) :
    (D.coordinateDenominator : ℚ) * D.anchorCoordinate r =
      (D.anchorIntegerCoordinate r : ℚ) := by
  rcases r with r | j
  · simp only [anchorCoordinate, anchorIntegerCoordinate, mul_neg, Int.cast_neg,
      D.coordinateDenominator_mul_deadline hplus hminus r]
  · simp only [anchorCoordinate, anchorIntegerCoordinate, mul_sub, mul_neg,
      Int.cast_sub, Int.cast_neg, coordinateDenominator, geomDenominator_mul_baseline,
      geomDenominator_mul_beta]

theorem coordinateDenominator_mul_globalCoordinate (r : D.GlobalCopy) :
    (D.coordinateDenominator : ℚ) * D.globalCoordinate r =
      (D.globalIntegerCoordinate r : ℚ) := by
  rcases r with ⟨species, j⟩
  cases species with
  | up b =>
      cases b <;> simp [globalCoordinate, globalIntegerCoordinate, coordinateDenominator]
  | um b =>
      cases b <;> simp [globalCoordinate, globalIntegerCoordinate, coordinateDenominator]
  | edge e b =>
      cases b <;>
        simp [globalCoordinate, globalIntegerCoordinate, mul_add, coordinateDenominator,
          geomDenominator_mul_beta, geomDenominator_mul_delta]

theorem coordinateDenominator_mul_localCoordinate {v : D.Vertex} (r : D.LocalAt v) :
    (D.coordinateDenominator : ℚ) * D.localCoordinate r =
      (D.localIntegerCoordinate r : ℚ) := by
  rcases r with (⟨ell, j⟩ | j) | j
  · have hell : ell.val ≤ D.L := (Finset.mem_Icc.mp ell.property).2
    simp only [localCoordinate, localLength, localIntegerCoordinate, mul_neg,
      Int.cast_neg, Int.cast_natCast, coordinateDenominator,
      geomDenominator_mul_lambda D.graph.edges.length D.R D.geometryBound D.L ell.val hell]
  · simp [localCoordinate, localLength, localIntegerCoordinate]
  · simp [localCoordinate, localLength, localIntegerCoordinate]

include hplus hminus in
theorem coordinateDenominator_mul_itemCoordinate (i : D.Item) :
    (D.coordinateDenominator : ℚ) * D.itemCoordinate i =
      (D.itemIntegerCoordinate i : ℚ) := by
  rcases i with ⟨r, i⟩
  cases r with
  | x => exact D.coordinateDenominator_mul_rowCoordinate hplus hminus i.2
  | anchor => exact D.coordinateDenominator_mul_anchorCoordinate hplus hminus i.2
  | «global» => exact D.coordinateDenominator_mul_globalCoordinate i
  | «local» => exact D.coordinateDenominator_mul_localCoordinate i.2
  | flag => simp [itemCoordinate, itemIntegerCoordinate]

include hplus hminus in
theorem itemIntegerCoordinate_ratio (i : D.Item) :
    (D.itemIntegerCoordinate i : ℚ) / D.coordinateDenominator = D.itemCoordinate i := by
  have hd : (D.coordinateDenominator : ℚ) ≠ 0 := by
    exact_mod_cast D.coordinateDenominator_pos.ne'
  apply (div_eq_iff hd).mpr
  simpa only [mul_comm] using
    (D.coordinateDenominator_mul_itemCoordinate hplus hminus i).symm

def itemRawPair (i : D.Item) : ℕ × ℕ :=
  rawItem D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
    (D.itemIntegerCoordinate i)

include hplus hminus in
theorem itemRawPair_valid (i : D.Item) :
    0 < (D.itemRawPair i).1 ∧ (D.itemRawPair i).1 < (D.itemRawPair i).2 := by
  apply rawItem_valid D.coordinateDenominator D.coordinateDenominator_pos
  rw [D.itemIntegerCoordinate_ratio hplus hminus i]
  exact D.itemCoordinate_abs_le_six i

include hplus hminus in
theorem itemRawPair_ratio (i : D.Item) :
    ((D.itemRawPair i).1 : ℚ) / (D.itemRawPair i).2 = D.itemSize i := by
  have hW : |(D.itemIntegerCoordinate i : ℚ) / D.coordinateDenominator| ≤ 6 := by
    rw [D.itemIntegerCoordinate_ratio hplus hminus i]
    exact D.itemCoordinate_abs_le_six i
  change ((rawItem _ _ _ _).1 : ℚ) / (rawItem _ _ _ _).2 = _
  rw [rawItem_ratio D.coordinateDenominator D.coordinateDenominator_pos _ _ _ hW,
    D.itemIntegerCoordinate_ratio hplus hminus i]
  rfl

end BinPackingGap.InventoryData

namespace BinPackingGap.NaturalPackingNumerator

open IntegerPackingArithmetic

structure NatDifference where
  pos : Nat
  neg : Nat
  deriving DecidableEq

namespace NatDifference

def eval (a : NatDifference) : Int := (a.pos : Int) - a.neg

def ofNat (n : Nat) : NatDifference := ⟨n, 0⟩

def ofInt (z : Int) : NatDifference := ⟨z.toNat, (-z).toNat⟩

def negate (a : NatDifference) : NatDifference := ⟨a.neg, a.pos⟩

def add (a b : NatDifference) : NatDifference := ⟨a.pos + b.pos, a.neg + b.neg⟩

def sub (a b : NatDifference) : NatDifference := ⟨a.pos + b.neg, a.neg + b.pos⟩

def scale (n : Nat) (a : NatDifference) : NatDifference := ⟨n * a.pos, n * a.neg⟩

def toNat (a : NatDifference) : Nat := a.pos - a.neg

@[simp] theorem eval_ofNat (n : Nat) : (ofNat n).eval = (n : Int) := by
  simp [ofNat, eval]

@[simp] theorem eval_ofInt (z : Int) : (ofInt z).eval = z :=
  Int.toNat_sub_toNat_neg z

@[simp] theorem eval_negate (a : NatDifference) : a.negate.eval = -a.eval := by
  simp only [negate, eval]
  ring

@[simp] theorem eval_add (a b : NatDifference) : (a.add b).eval = a.eval + b.eval := by
  simp only [add, eval, Nat.cast_add]
  ring

@[simp] theorem eval_sub (a b : NatDifference) : (a.sub b).eval = a.eval - b.eval := by
  simp only [sub, eval, Nat.cast_add]
  ring

@[simp] theorem eval_scale (n : Nat) (a : NatDifference) :
    (scale n a).eval = (n : Int) * a.eval := by
  simp only [scale, eval, Nat.cast_mul]
  ring

theorem toNat_eq (a : NatDifference) : a.toNat = a.eval.toNat := by
  unfold toNat eval
  omega

end NatDifference

def baselineParts (m R D L : Nat) (r : Geometry.Position m R) : NatDifference :=
  ⟨80 * (R + 1) ^ m * widthRadix D ^ L +
      10 * widthRadix D ^ L * (r.2.val + 1) * (R + 1) ^ r.1.val,
    10 * widthRadix D ^ L⟩

def betaParts (m R D L : Nat) (edge : Fin m) : NatDifference :=
  ⟨10 * widthRadix D ^ L * (R + 1) ^ edge.val, 10 * widthRadix D ^ L⟩

@[simp] theorem eval_baselineParts (m R D L : Nat) (r : Geometry.Position m R) :
    (baselineParts m R D L r).eval = baselineNumerator m R D L r := by
  simp only [baselineParts, NatDifference.eval, baselineNumerator, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring

@[simp] theorem eval_betaParts (m R D L : Nat) (edge : Fin m) :
    (betaParts m R D L edge).eval = betaNumerator m R D L edge := by
  simp only [betaParts, NatDifference.eval, betaNumerator, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring

section Coordinates

variable (D : InventoryData)

def treeBaselineParts : D.TreeRow → NatDifference
  | .inl (node, _) => NatDifference.ofNat
      (treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val)
  | .inr (.inl (node, _)) => NatDifference.ofNat
      (treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val)
  | .inr (.inr _) => NatDifference.ofNat D.coordinateDenominator

def rowBaselineParts {v : D.Vertex} : D.RowAt v → NatDifference
  | .inl r => treeBaselineParts D r
  | .inr (_, j) => baselineParts D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j)

def treeDeadlineParts : D.TreeRow → NatDifference
  | .inl (node, _) => NatDifference.ofNat
      (if node.val ∈ D.plus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val)
  | .inr (.inl (node, _)) => NatDifference.ofNat
      (if node.val ∈ D.minus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val)
  | .inr (.inr _) => NatDifference.ofNat D.coordinateDenominator

def deadlineParts {v : D.Vertex} : D.MBase v → NatDifference
  | .inl r => treeDeadlineParts D r
  | .inr j => (baselineParts D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)).sub (NatDifference.ofNat 1)

def rowParts {v : D.Vertex} (r : D.RowAt v) : NatDifference :=
  (rowBaselineParts D r).sub (NatDifference.ofNat (if D.rowShort r then 1 else 0))

def anchorParts {v : D.Vertex} : D.AnchorAt v → NatDifference
  | .inl z => (deadlineParts D z).negate
  | .inr j => (baselineParts D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)).negate.sub
        (betaParts D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j).1)

def globalParts : D.GlobalCopy → NatDifference
  | ⟨.up one, _⟩ => (NatDifference.ofNat (if one then D.coordinateDenominator else 0)).negate
  | ⟨.um one, _⟩ => (NatDifference.ofNat (if one then D.coordinateDenominator else 0)).negate
  | ⟨.edge edge permit, _⟩ =>
      (betaParts D.graph.edges.length D.R D.geometryBound D.L edge).add
        (NatDifference.ofNat (if permit then 0 else 1))

def localParts {v : D.Vertex} : D.LocalAt v → NatDifference
  | .inl (.inl ⟨ell, _⟩) =>
      (NatDifference.ofNat (localNumerator D.geometryBound D.L ell.val)).negate
  | _ => NatDifference.ofNat 0

def coordinateParts : D.Item → NatDifference
  | ⟨.x, ⟨_, r⟩⟩ => rowParts D r
  | ⟨.anchor, ⟨_, a⟩⟩ => anchorParts D a
  | ⟨.«global», u⟩ => globalParts D u
  | ⟨.«local», ⟨_, l⟩⟩ => localParts D l
  | ⟨.flag, _⟩ => NatDifference.ofNat 0

@[simp] theorem eval_treeBaselineParts (r : D.TreeRow) :
    (treeBaselineParts D r).eval = D.treeBaselineInteger r := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j) <;>
    simp [treeBaselineParts, InventoryData.treeBaselineInteger]

@[simp] theorem eval_rowBaselineParts {v : D.Vertex} (r : D.RowAt v) :
    (rowBaselineParts D r).eval = D.rowBaselineInteger r := by
  rcases r with r | ⟨b, j⟩ <;>
    simp [rowBaselineParts, InventoryData.rowBaselineInteger]

@[simp] theorem eval_treeDeadlineParts (r : D.TreeRow) :
    (treeDeadlineParts D r).eval = D.treeDeadlineInteger r := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · by_cases h : node.val ∈ D.plus.leaves <;>
      simp [treeDeadlineParts, InventoryData.treeDeadlineInteger, h]
  · by_cases h : node.val ∈ D.minus.leaves <;>
      simp [treeDeadlineParts, InventoryData.treeDeadlineInteger, h]
  · simp [treeDeadlineParts, InventoryData.treeDeadlineInteger]

@[simp] theorem eval_deadlineParts {v : D.Vertex} (r : D.MBase v) :
    (deadlineParts D r).eval = D.deadlineInteger r := by
  rcases r with r | j <;>
    simp [deadlineParts, InventoryData.deadlineInteger]

@[simp] theorem eval_rowParts {v : D.Vertex} (r : D.RowAt v) :
    (rowParts D r).eval = D.rowIntegerCoordinate r := by
  cases h : D.rowShort r <;>
    simp [rowParts, InventoryData.rowIntegerCoordinate, h]

@[simp] theorem eval_anchorParts {v : D.Vertex} (r : D.AnchorAt v) :
    (anchorParts D r).eval = D.anchorIntegerCoordinate r := by
  rcases r with r | j <;>
    simp [anchorParts, InventoryData.anchorIntegerCoordinate]

@[simp] theorem eval_globalParts (r : D.GlobalCopy) :
    (globalParts D r).eval = D.globalIntegerCoordinate r := by
  rcases r with ⟨species, j⟩
  cases species with
  | up b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]
  | um b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]
  | edge e b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]

@[simp] theorem eval_localParts {v : D.Vertex} (r : D.LocalAt v) :
    (localParts D r).eval = D.localIntegerCoordinate r := by
  rcases r with (⟨ell, j⟩ | j) | j <;>
    simp [localParts, InventoryData.localIntegerCoordinate]

@[simp] theorem eval_coordinateParts (i : D.Item) :
    (coordinateParts D i).eval = D.itemIntegerCoordinate i := by
  rcases i with ⟨role, i⟩
  cases role with
  | x => exact eval_rowParts D i.2
  | anchor => exact eval_anchorParts D i.2
  | «global» => exact eval_globalParts D i
  | «local» => exact eval_localParts D i.2
  | flag => simp [coordinateParts, InventoryData.itemIntegerCoordinate]

end Coordinates

def primaryParts (subclass : Subclass) : NatDifference := NatDifference.ofInt (primaryScore subclass)

@[simp] theorem eval_primaryParts (subclass : Subclass) :
    (primaryParts subclass).eval = primaryScore subclass :=
  NatDifference.eval_ofInt _

def labelPower {n : Nat} (label : Option (Fin n)) : Nat :=
  label.elim 0 (fun v => 3 ^ (v.val + 1))

def secondaryParts {n : Nat} (subclass : Subclass) (label : Option (Fin n)) : NatDifference :=
  match subclass.role with
  | .x => NatDifference.ofNat (labelPower label)
  | .anchor => (NatDifference.ofNat (2 * labelPower label)).negate
  | .«global» => NatDifference.ofNat 0
  | .«local» => NatDifference.ofNat (labelPower label)
  | .flag => NatDifference.ofNat 0

@[simp] theorem eval_secondaryParts {n : Nat} (subclass : Subclass) (label : Option (Fin n)) :
    (secondaryParts subclass label).eval = secondaryScore subclass label := by
  cases label <;> cases h : subclass.role <;>
    simp [secondaryParts, secondaryScore, labelPower, labelWeight, h]

def signedParts (n geom : Nat) (p q W : NatDifference) : NatDifference :=
  (((NatDifference.ofNat (200000000 * primaryBound * 3 ^ n * geom)).add
    (NatDifference.scale (1000000 * 3 ^ n * geom) p)).add
      (NatDifference.scale (1000 * geom) q)).add W

@[simp] theorem signedParts_pos (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).pos =
      200000000 * primaryBound * 3 ^ n * geom +
        (1000000 * 3 ^ n * geom) * p.pos + (1000 * geom) * q.pos + W.pos := rfl

@[simp] theorem signedParts_neg (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).neg =
      (1000000 * 3 ^ n * geom) * p.neg + (1000 * geom) * q.neg + W.neg := by
  simp [signedParts, NatDifference.ofNat, NatDifference.add, NatDifference.scale]

theorem signedParts_toNat (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).toNat =
      (200000000 * primaryBound * 3 ^ n * geom +
        (1000000 * 3 ^ n * geom) * p.pos + (1000 * geom) * q.pos + W.pos) -
      ((1000000 * 3 ^ n * geom) * p.neg + (1000 * geom) * q.neg + W.neg) := by
  simp only [NatDifference.toNat, signedParts_pos, signedParts_neg]

@[simp] theorem eval_signedParts (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).eval = signedNumerator n geom p.eval q.eval W.eval := by
  simp only [signedParts, NatDifference.eval_add, NatDifference.eval_ofNat,
    NatDifference.eval_scale, signedNumerator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

def numeratorParts {n : Nat} (geom : Nat) (subclass : Subclass) (label : Option (Fin n))
    (W : NatDifference) : NatDifference :=
  signedParts n geom (primaryParts subclass) (secondaryParts subclass label) W

@[simp] theorem eval_numeratorParts {n : Nat} (geom : Nat) (subclass : Subclass)
    (label : Option (Fin n)) (W : NatDifference) :
    (numeratorParts geom subclass label W).eval = itemNumerator geom subclass label W.eval := by
  simp [numeratorParts, itemNumerator]

theorem numeratorParts_toNat {n : Nat} (geom : Nat) (subclass : Subclass)
    (label : Option (Fin n)) (W : NatDifference) :
    (numeratorParts geom subclass label W).toNat = (itemNumerator geom subclass label W.eval).toNat := by
  rw [NatDifference.toNat_eq, eval_numeratorParts]

def inventoryParts (D : InventoryData) (i : D.Item) : NatDifference :=
  numeratorParts D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
    (coordinateParts D i)

def inventoryNumerator (D : InventoryData) (i : D.Item) : Nat :=
  (inventoryParts D i).toNat

theorem inventoryNumerator_eq (D : InventoryData) (i : D.Item) :
    inventoryNumerator D i =
      (itemNumerator D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
        (D.itemIntegerCoordinate i)).toNat := by
  simp only [inventoryNumerator, inventoryParts, numeratorParts_toNat, eval_coordinateParts]

def naturalRawItem (D : InventoryData) (i : D.Item) : Nat × Nat :=
  (inventoryNumerator D i, sizeDenominator D.graph.n D.coordinateDenominator)

theorem naturalRawItem_eq (D : InventoryData) (i : D.Item) :
    naturalRawItem D i = D.itemRawPair i := by
  simp only [naturalRawItem, InventoryData.itemRawPair, rawItem, inventoryNumerator_eq]

end BinPackingGap.NaturalPackingNumerator

namespace BinPackingGap.PackingCoordinateExpression

open IntegerPackingArithmetic
open NaturalPackingNumerator
open NatExpressionCompiler

inductive Input
  | geometryDg
  | totalPowerA
  | edgePower
  | repetitionOne
  deriving DecidableEq

instance : Fintype Input where
  elems := {.geometryDg, .totalPowerA, .edgePower, .repetitionOne}
  complete i := by cases i <;> simp

structure Parts where
  pos : Expr Input
  neg : Expr Input

namespace Parts

def eval (values : Input → Nat) (p : Parts) : NatDifference :=
  ⟨NatExpressionCompiler.eval values p.pos, NatExpressionCompiler.eval values p.neg⟩

def ofExpr (e : Expr Input) : Parts := ⟨e, .constant 0⟩
def negate (p : Parts) : Parts := ⟨p.neg, p.pos⟩
def add (p q : Parts) : Parts := ⟨.add p.pos q.pos, .add p.neg q.neg⟩
def sub (p q : Parts) : Parts := ⟨.add p.pos q.neg, .add p.neg q.pos⟩

@[simp] theorem eval_ofExpr (values : Input → Nat) (e : Expr Input) :
    (ofExpr e).eval values = NatDifference.ofNat (NatExpressionCompiler.eval values e) := rfl

@[simp] theorem eval_negate (values : Input → Nat) (p : Parts) :
    p.negate.eval values = (p.eval values).negate := rfl

@[simp] theorem eval_add (values : Input → Nat) (p q : Parts) :
    (p.add q).eval values = (p.eval values).add (q.eval values) := rfl

@[simp] theorem eval_sub (values : Input → Nat) (p q : Parts) :
    (p.sub q).eval values = (p.eval values).sub (q.eval values) := rfl

end Parts

inductive TreeDescriptor (plus minus : UniformTree)
  | plusNode (node : plus.Node)
  | minusNode (node : minus.Node)
  | padding
  deriving DecidableEq

instance (plus minus : UniformTree) : Fintype (TreeDescriptor plus minus) where
  elems := Finset.univ.image TreeDescriptor.plusNode ∪
    Finset.univ.image TreeDescriptor.minusNode ∪ {.padding}
  complete tree := by cases tree <;> simp

inductive Descriptor (plus minus : UniformTree) (L : Nat)
  | treeRow (tree : TreeDescriptor plus minus)
  | jobRow (short : Bool)
  | treeAnchor (tree : TreeDescriptor plus minus)
  | jobAnchor
  | jobKey
  | globalUnit (one : Bool)
  | globalEdge (permit : Bool)
  | localDepth (depth : Fin (L + 1))
  | zero
  deriving DecidableEq

instance (plus minus : UniformTree) (L : Nat) : Fintype (Descriptor plus minus L) where
  elems := Finset.univ.image Descriptor.treeRow ∪
    Finset.univ.image Descriptor.jobRow ∪
    Finset.univ.image Descriptor.treeAnchor ∪
    {.jobAnchor, .jobKey, .zero} ∪
    Finset.univ.image Descriptor.globalUnit ∪
    Finset.univ.image Descriptor.globalEdge ∪
    Finset.univ.image Descriptor.localDepth
  complete descriptor := by cases descriptor <;> simp

def treeLeftExpr (bound L : Nat) (side : TreeGeometry.Side) (address : List Nat) :
    Expr Input :=
  .add (.mul (.constant (rootOffsetNumerator side)) (.input .geometryDg))
    (.constant (pathNumerator bound L 0 address))

def treeRightExpr (bound L : Nat) (side : TreeGeometry.Side) (address : List Nat) :
    Expr Input :=
  .add (treeLeftExpr bound L side address)
    (if address = [] then .input .geometryDg
      else .constant (localNumerator bound L address.length))

def treeBaselineExpr {plus minus : UniformTree} (bound L : Nat) :
    TreeDescriptor plus minus → Parts
  | .plusNode node => Parts.ofExpr (treeRightExpr bound L .plus node.val)
  | .minusNode node => Parts.ofExpr (treeRightExpr bound L .minus node.val)
  | .padding => Parts.ofExpr (.input .geometryDg)

def treeDeadlineExpr {plus minus : UniformTree} (bound L : Nat) :
    TreeDescriptor plus minus → Parts
  | .plusNode node => Parts.ofExpr
      (if node.val ∈ plus.leaves then treeLeftExpr bound L .plus node.val
        else treeRightExpr bound L .plus node.val)
  | .minusNode node => Parts.ofExpr
      (if node.val ∈ minus.leaves then treeLeftExpr bound L .minus node.val
        else treeRightExpr bound L .minus node.val)
  | .padding => Parts.ofExpr (.input .geometryDg)

def baselineExpr (bound L : Nat) : Parts :=
  ⟨.add
      (.mul (.mul (.constant 80) (.input .totalPowerA))
        (.constant (widthRadix bound ^ L)))
      (.mul
        (.mul (.constant (10 * widthRadix bound ^ L)) (.input .repetitionOne))
        (.input .edgePower)),
    .constant (10 * widthRadix bound ^ L)⟩

def betaExpr (bound L : Nat) : Parts :=
  ⟨.mul (.constant (10 * widthRadix bound ^ L)) (.input .edgePower),
    .constant (10 * widthRadix bound ^ L)⟩

def expression {plus minus : UniformTree} {L : Nat} (bound : Nat) :
    Descriptor plus minus L → Parts
  | .treeRow tree => (treeBaselineExpr bound L tree).sub (Parts.ofExpr (.constant 0))
  | .jobRow short => (baselineExpr bound L).sub
      (Parts.ofExpr (.constant (if short then 1 else 0)))
  | .treeAnchor tree => (treeDeadlineExpr bound L tree).negate
  | .jobAnchor => ((baselineExpr bound L).sub (Parts.ofExpr (.constant 1))).negate
  | .jobKey => (baselineExpr bound L).negate.sub (betaExpr bound L)
  | .globalUnit one =>
      (Parts.ofExpr (if one then .input .geometryDg else .constant 0)).negate
  | .globalEdge permit => (betaExpr bound L).add
      (Parts.ofExpr (.constant (if permit then 0 else 1)))
  | .localDepth depth =>
      (Parts.ofExpr (.constant (localNumerator bound L depth.val))).negate
  | .zero => Parts.ofExpr (.constant 0)

def registers (D : InventoryData) (edge repetitionOne : Nat) : Input → Nat
  | .geometryDg => D.coordinateDenominator
  | .totalPowerA => (D.R + 1) ^ D.graph.edges.length
  | .edgePower => (D.R + 1) ^ edge
  | .repetitionOne => repetitionOne

def treeDescriptor (D : InventoryData) : D.TreeRow → TreeDescriptor D.plus D.minus
  | .inl (node, _) => .plusNode node
  | .inr (.inl (node, _)) => .minusNode node
  | .inr (.inr _) => .padding

def coordinateDescriptor (D : InventoryData) : D.Item → Descriptor D.plus D.minus D.L
  | ⟨.x, ⟨_, .inl tree⟩⟩ => .treeRow (treeDescriptor D tree)
  | ⟨.x, ⟨_, .inr (short, _)⟩⟩ => .jobRow short
  | ⟨.anchor, ⟨_, .inl (.inl tree)⟩⟩ => .treeAnchor (treeDescriptor D tree)
  | ⟨.anchor, ⟨_, .inl (.inr _)⟩⟩ => .jobAnchor
  | ⟨.anchor, ⟨_, .inr _⟩⟩ => .jobKey
  | ⟨.«global», ⟨.up one, _⟩⟩ => .globalUnit one
  | ⟨.«global», ⟨.um one, _⟩⟩ => .globalUnit one
  | ⟨.«global», ⟨.edge _ permit, _⟩⟩ => .globalEdge permit
  | ⟨.«local», ⟨_, .inl (.inl ⟨depth, _⟩)⟩⟩ =>
      .localDepth ⟨depth.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp depth.property).2⟩
  | ⟨.«local», _⟩ => .zero
  | ⟨.flag, _⟩ => .zero

def edgeIndex (D : InventoryData) : D.Item → Nat
  | ⟨.x, ⟨_, .inr (_, job)⟩⟩ => (D.jobPosition job).1.val
  | ⟨.anchor, ⟨_, .inl (.inr job)⟩⟩ => (D.jobPosition job).1.val
  | ⟨.anchor, ⟨_, .inr job⟩⟩ => (D.jobPosition job).1.val
  | ⟨.«global», ⟨.edge edge _, _⟩⟩ => edge.val
  | _ => 0

def repetitionOne (D : InventoryData) : D.Item → Nat
  | ⟨.x, ⟨_, .inr (_, job)⟩⟩ => (D.jobPosition job).2.val + 1
  | ⟨.anchor, ⟨_, .inl (.inr job)⟩⟩ => (D.jobPosition job).2.val + 1
  | ⟨.anchor, ⟨_, .inr job⟩⟩ => (D.jobPosition job).2.val + 1
  | _ => 0

def coordinateValues (D : InventoryData) (i : D.Item) : Input → Nat :=
  registers D (edgeIndex D i) (repetitionOne D i)

@[simp] theorem eval_treeLeftExpr (D : InventoryData) (edge rep : Nat)
    (side : TreeGeometry.Side) (address : List Nat) :
    NatExpressionCompiler.eval (registers D edge rep)
        (treeLeftExpr D.geometryBound D.L side address) =
      treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L side address := rfl

@[simp] theorem eval_treeRightExpr (D : InventoryData) (edge rep : Nat)
    (side : TreeGeometry.Side) (address : List Nat) :
    NatExpressionCompiler.eval (registers D edge rep)
        (treeRightExpr D.geometryBound D.L side address) =
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L side address := by
  by_cases h : address = [] <;>
    simp [treeRightExpr, treeRightNumerator, h, registers, InventoryData.coordinateDenominator]

@[simp] theorem eval_treeBaselineExpr (D : InventoryData) (edge rep : Nat) (r : D.TreeRow) :
    (treeBaselineExpr D.geometryBound D.L (treeDescriptor D r)).eval (registers D edge rep) =
      treeBaselineParts D r := by
  rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy) <;>
    simp [treeDescriptor, treeBaselineExpr, treeBaselineParts, registers]

@[simp] theorem eval_treeDeadlineExpr (D : InventoryData) (edge rep : Nat) (r : D.TreeRow) :
    (treeDeadlineExpr D.geometryBound D.L (treeDescriptor D r)).eval (registers D edge rep) =
      treeDeadlineParts D r := by
  rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy)
  · by_cases h : node.val ∈ D.plus.leaves <;>
      simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, h]
  · by_cases h : node.val ∈ D.minus.leaves <;>
      simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, h]
  · simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, registers]

@[simp] theorem eval_baselineExpr (D : InventoryData) (edge rep : Nat) :
    (baselineExpr D.geometryBound D.L).eval (registers D edge rep) =
      ⟨80 * (D.R + 1) ^ D.graph.edges.length * widthRadix D.geometryBound ^ D.L +
        10 * widthRadix D.geometryBound ^ D.L * rep * (D.R + 1) ^ edge,
        10 * widthRadix D.geometryBound ^ D.L⟩ := rfl

@[simp] theorem eval_betaExpr (D : InventoryData) (edge rep : Nat) :
    (betaExpr D.geometryBound D.L).eval (registers D edge rep) =
      ⟨10 * widthRadix D.geometryBound ^ D.L * (D.R + 1) ^ edge,
        10 * widthRadix D.geometryBound ^ D.L⟩ := rfl

theorem eval_coordinateDescriptor (D : InventoryData) (i : D.Item) :
    (expression D.geometryBound (coordinateDescriptor D i)).eval (coordinateValues D i) =
      coordinateParts D i := by
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
      rcases i with ⟨v, tree | ⟨short, job⟩⟩
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, rowParts, rowBaselineParts, InventoryData.rowShort]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, rowParts, rowBaselineParts, InventoryData.rowShort, baselineParts]
        rfl
  | anchor =>
      rcases i with ⟨v, (tree | job) | job⟩
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, deadlineParts]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, deadlineParts, baselineParts]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, baselineParts, betaParts]
  | «global» =>
      rcases i with ⟨species, copy⟩
      cases species with
      | up one => cases one <;> simp [coordinateDescriptor, expression, coordinateValues, edgeIndex,
          repetitionOne, coordinateParts, globalParts, registers]
      | um one => cases one <;> simp [coordinateDescriptor, expression, coordinateValues, edgeIndex,
          repetitionOne, coordinateParts, globalParts, registers]
      | edge edge permit => simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, globalParts, betaParts]
  | «local» =>
      rcases i with ⟨v, (⟨depth, copy⟩ | (zero | job)) | job⟩ <;>
        simp [coordinateDescriptor, expression, coordinateParts, localParts]
  | flag => simp [coordinateDescriptor, expression, coordinateParts]

theorem eval_coordinate_pos (D : InventoryData) (i : D.Item) :
    NatExpressionCompiler.eval (coordinateValues D i)
        (expression D.geometryBound (coordinateDescriptor D i)).pos =
      (coordinateParts D i).pos :=
  congrArg NatDifference.pos (eval_coordinateDescriptor D i)

theorem eval_coordinate_neg (D : InventoryData) (i : D.Item) :
    NatExpressionCompiler.eval (coordinateValues D i)
        (expression D.geometryBound (coordinateDescriptor D i)).neg =
      (coordinateParts D i).neg :=
  congrArg NatDifference.neg (eval_coordinateDescriptor D i)

theorem eval_coordinate_integer (D : InventoryData) (i : D.Item) :
    ((expression D.geometryBound (coordinateDescriptor D i)).eval (coordinateValues D i)).eval =
      D.itemIntegerCoordinate i := by
  rw [eval_coordinateDescriptor, eval_coordinateParts]

end BinPackingGap.PackingCoordinateExpression

namespace BinPackingGap.PackingScalarExpression

open NatExpressionCompiler NaturalPackingNumerator IntegerPackingArithmetic

inductive Variable
  | vertexPower | geometry | labelPower | coordinatePositive | coordinateNegative
  deriving DecidableEq

instance : Fintype Variable where
  elems := {.vertexPower, .geometry, .labelPower, .coordinatePositive, .coordinateNegative}
  complete v := by cases v <;> simp

def values {n : Nat} (geom : Nat) (label : Option (Fin n)) (W : NatDifference) :
    Variable → Nat
  | .vertexPower => 3 ^ n
  | .geometry => geom
  | .labelPower => NaturalPackingNumerator.labelPower label
  | .coordinatePositive => W.pos
  | .coordinateNegative => W.neg

def baseTerm : Expr Variable :=
  .mul (.mul (.constant (200000000 * primaryBound)) (.input .vertexPower))
    (.input .geometry)

def primaryFactor : Expr Variable :=
  .mul (.mul (.constant 1000000) (.input .vertexPower)) (.input .geometry)

def secondaryFactor : Expr Variable := .mul (.constant 1000) (.input .geometry)

def positiveLabel (subclass : Subclass) : Expr Variable :=
  match subclass.role with
  | .x => .input .labelPower
  | .«local» => .input .labelPower
  | _ => .constant 0

def negativeLabel (subclass : Subclass) : Expr Variable :=
  match subclass.role with
  | .anchor => .mul (.constant 2) (.input .labelPower)
  | _ => .constant 0

def positiveTerm (subclass : Subclass) : Expr Variable :=
  .add (.add (.add baseTerm
    (.mul primaryFactor (.constant (primaryParts subclass).pos)))
    (.mul secondaryFactor (positiveLabel subclass))) (.input .coordinatePositive)

def negativeTerm (subclass : Subclass) : Expr Variable :=
  .add (.add (.mul primaryFactor (.constant (primaryParts subclass).neg))
    (.mul secondaryFactor (negativeLabel subclass))) (.input .coordinateNegative)

def numerator (subclass : Subclass) : Expr Variable :=
  .monus (positiveTerm subclass) (negativeTerm subclass)

def denominator : Expr Variable :=
  .mul (.mul (.constant (10 ^ 9 * primaryBound)) (.input .vertexPower))
    (.input .geometry)

theorem eval_positiveLabel {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (positiveLabel subclass) = (secondaryParts subclass label).pos := by
  cases h : subclass.role <;>
    simp [positiveLabel, secondaryParts, h, values, NatDifference.ofNat,
      NatDifference.negate]

theorem eval_negativeLabel {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (negativeLabel subclass) = (secondaryParts subclass label).neg := by
  cases h : subclass.role <;>
    simp [negativeLabel, secondaryParts, h, eval, values, NatDifference.ofNat,
      NatDifference.negate]

theorem eval_positiveTerm {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (positiveTerm subclass) =
      (numeratorParts geom subclass label W).pos := by
  simp only [positiveTerm, eval_add, eval_mul, eval_constant, eval_input,
    eval_positiveLabel, numeratorParts, signedParts_pos]
  rfl

theorem eval_negativeTerm {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (negativeTerm subclass) =
      (numeratorParts geom subclass label W).neg := by
  simp only [negativeTerm, eval_add, eval_mul, eval_constant, eval_input,
    eval_negativeLabel, numeratorParts, signedParts_neg]
  rfl

theorem eval_numerator {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (numerator subclass) =
      (numeratorParts geom subclass label W).toNat := by
  simp only [numerator, eval_monus, eval_positiveTerm, eval_negativeTerm,
    NatDifference.toNat]

theorem eval_denominator {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) :
    eval (values geom label W) denominator = sizeDenominator n geom := rfl

theorem eval_item_numerator (D : InventoryData) (i : D.Item) :
    eval (values D.coordinateDenominator (D.itemLabel i) (coordinateParts D i))
        (numerator (D.itemSubclass i)) = (D.itemRawPair i).1 := by
  rw [eval_numerator]
  change inventoryNumerator D i = _
  exact congrArg Prod.fst (naturalRawItem_eq D i)

theorem eval_item_denominator (D : InventoryData) (i : D.Item) :
    eval (values D.coordinateDenominator (D.itemLabel i) (coordinateParts D i))
      denominator = (D.itemRawPair i).2 := rfl

end BinPackingGap.PackingScalarExpression

end OAI
