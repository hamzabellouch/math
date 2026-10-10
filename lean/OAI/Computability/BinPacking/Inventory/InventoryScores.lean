import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Packing.K4Graph
import OAI.Computability.BinPacking.Trees.IntegerTreeGeometry

namespace OAI

namespace BinPackingGap

open scoped BigOperators

structure InventoryData where
  graph : GraphInput
  plus : UniformTree
  minus : UniformTree
  d : ℕ
  R : ℕ
  L : ℕ
  quota : ℕ → ℕ
  k : ℕ

namespace InventoryData

variable (D : InventoryData)

abbrev Vertex := D.graph.Vertex
abbrev Edge := D.graph.Edge
abbrev Position := D.graph.Edge × Fin D.R
abbrev IncidencePosition (v : D.Vertex) := D.graph.IncidencePosition D.R v
abbrev JobCopy (v : D.Vertex) := D.graph.JobCopy D.R D.d v
abbrev Depth := {ell : ℕ // ell ∈ Finset.Icc 1 D.L}

def P : ℕ := ∑ ell ∈ Finset.Icc 1 D.L, D.quota ell

def tPlus : ℕ := D.d * Fintype.card D.plus.Node + D.P
def tMinus : ℕ := D.d * Fintype.card D.minus.Node
def t : ℕ := D.tPlus + D.tMinus
def J (v : D.Vertex) : ℕ := D.d * D.R * D.graph.degree v
def B : ℕ := ∑ v : D.Vertex, (D.t + 2 * D.J v)

abbrev TreeRow :=
  (D.plus.Node × Fin D.d) ⊕ ((D.minus.Node × Fin D.d) ⊕ Fin D.P)

abbrev RowAt (v : D.Vertex) := D.TreeRow ⊕ (Bool × D.JobCopy v)

abbrev MBase (v : D.Vertex) := D.TreeRow ⊕ D.JobCopy v

abbrev AnchorAt (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

abbrev PositiveLocal := Σ ell : D.Depth, Fin (D.quota ell.val)

abbrev ZeroLocalAt (v : D.Vertex) := Fin (D.t - D.P) ⊕ D.JobCopy v
abbrev DMAt (v : D.Vertex) := D.PositiveLocal ⊕ D.ZeroLocalAt v
abbrev LocalAt (v : D.Vertex) := D.DMAt v ⊕ D.JobCopy v

abbrev LocalBin (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

abbrev PlusLeaf := {v : D.plus.Node // v.val ∈ D.plus.leaves}
abbrev MinusLeaf := {v : D.minus.Node // v.val ∈ D.minus.leaves}
abbrev TestAt (v : D.Vertex) :=
  D.PlusLeaf ⊕ (D.MinusLeaf ⊕ D.IncidencePosition v)

def designated {v : D.Vertex} : D.TestAt v × Fin D.d → D.MBase v
  | ⟨.inl leaf, j⟩ => .inl (.inl (leaf.val, j))
  | ⟨.inr (.inl leaf), j⟩ => .inl (.inr (.inl (leaf.val, j)))
  | ⟨.inr (.inr r), j⟩ => .inr (r, j)

def plusSlots : ℕ := ∑ v : D.Vertex, (D.tPlus + D.J v)
def minusSlots : ℕ := D.graph.n * D.tMinus
def treeFlags : ℕ := D.graph.n * D.t
def jobFlags : ℕ := ∑ v : D.Vertex, D.J v

end InventoryData

inductive GlobalSpecies (G : GraphInput) where
  | up (unitLength : Bool)
  | um (unitLength : Bool)
  | edge (e : G.Edge) (permit : Bool)
  deriving DecidableEq

instance (G : GraphInput) : Fintype (GlobalSpecies G) where
  elems := (Finset.univ.image GlobalSpecies.up) ∪
    (Finset.univ.image GlobalSpecies.um) ∪
    ((Finset.univ : Finset (G.Edge × Bool)).image
      (fun p => GlobalSpecies.edge p.1 p.2))
  complete := by
    intro s
    cases s <;> simp

inductive FlagSpecies where
  | tree
  | main
  | edge
  deriving DecidableEq

instance : Fintype FlagSpecies where
  elems := {.tree, .main, .edge}
  complete := by intro s; cases s <;> simp

namespace InventoryData

variable (D : InventoryData)

def globalStock : GlobalSpecies D.graph → ℕ
  | .up true => D.d * D.k
  | .up false => D.plusSlots - D.d * D.k
  | .um true => D.d * (D.graph.n - D.k)
  | .um false => D.minusSlots - D.d * (D.graph.n - D.k)
  | .edge _ _ => D.d * D.R

def flagStock : FlagSpecies → ℕ
  | .tree => D.treeFlags
  | .main => D.jobFlags
  | .edge => D.jobFlags

abbrev GlobalCopy := Σ s : GlobalSpecies D.graph, Fin (D.globalStock s)
abbrev FlagCopy := Σ s : FlagSpecies, Fin (D.flagStock s)

def RoleCopies : Role → Type
  | .x => Σ v : D.Vertex, D.RowAt v
  | .anchor => Σ v : D.Vertex, D.AnchorAt v
  | .«global» => D.GlobalCopy
  | .«local» => Σ v : D.Vertex, D.LocalAt v
  | .flag => D.FlagCopy

instance roleCopiesFintype (r : Role) : Fintype (D.RoleCopies r) := by
  cases r <;> dsimp [RoleCopies] <;> infer_instance

abbrev Item := Σ r : Role, D.RoleCopies r

def itemRole (i : D.Item) : Role := i.1

def itemLabel : D.Item → Option D.Vertex
  | ⟨.x, x⟩ => some x.1
  | ⟨.anchor, a⟩ => some a.1
  | ⟨.«global», _⟩ => none
  | ⟨.«local», a⟩ => some a.1
  | ⟨.flag, _⟩ => none

def treeSubclass : D.TreeRow → Subclass
  | .inl _ => .tp
  | .inr (.inl _) => .tm
  | .inr (.inr _) => .tp

def rowSubclass {v : D.Vertex} : D.RowAt v → Subclass
  | .inl t => D.treeSubclass t
  | .inr _ => .s

def itemSubclass : D.Item → Subclass
  | ⟨.x, ⟨_, r⟩⟩ => D.rowSubclass r
  | ⟨.anchor, ⟨_, .inl _⟩⟩ => .z
  | ⟨.anchor, ⟨_, .inr _⟩⟩ => .y
  | ⟨.«global», ⟨.up _, _⟩⟩ => .up
  | ⟨.«global», ⟨.um _, _⟩⟩ => .um
  | ⟨.«global», ⟨.edge _ _, _⟩⟩ => .w
  | ⟨.«local», ⟨_, .inl _⟩⟩ => .dm
  | ⟨.«local», ⟨_, .inr _⟩⟩ => .dg
  | ⟨.flag, ⟨.tree, _⟩⟩ => .ft
  | ⟨.flag, ⟨.main, _⟩⟩ => .fm
  | ⟨.flag, ⟨.edge, _⟩⟩ => .fg

theorem itemSubclass_role (i : D.Item) : (D.itemSubclass i).role = D.itemRole i := by
  rcases i with ⟨r, i⟩
  cases r with
  | x =>
      rcases i with ⟨v, (row | job)⟩
      · rcases row with (plus | (minus | padding)) <;> rfl
      · rfl
  | anchor => rcases i with ⟨v, (deadline | key)⟩ <;> rfl
  | «global» =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl
  | «local» => rcases i with ⟨v, (main | edge)⟩ <;> rfl
  | flag =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl

def rowShort {v : D.Vertex} : D.RowAt v → Bool
  | .inl _ => false
  | .inr r => r.1

def jobPosition {v : D.Vertex} (j : D.JobCopy v) : D.Position :=
  (j.1.1.val.1, j.1.2)

def rowPosition {v : D.Vertex} : D.RowAt v → Option D.Position
  | .inl _ => none
  | .inr r => some (D.jobPosition r.2)

def keyPosition {v : D.Vertex} (k : D.JobCopy v) : D.Position :=
  D.jobPosition k

def globalUnit : D.GlobalCopy → Bool
  | ⟨.up unit, _⟩ => unit
  | ⟨.um unit, _⟩ => unit
  | ⟨.edge _ _, _⟩ => false

def globalEdge : D.GlobalCopy → Option D.Edge
  | ⟨.edge e _, _⟩ => some e
  | _ => none

def globalPermit : D.GlobalCopy → Bool
  | ⟨.edge _ permit, _⟩ => permit
  | _ => false

def localDepth {v : D.Vertex} : D.LocalAt v → Option D.Depth
  | .inl (.inl p) => some p.1
  | _ => none

end InventoryData

theorem sum_primaryScore_eq_zero_of_inventory {ι : Type*} [Fintype ι]
    (s : ι → Subclass) (B : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hrole : ∀ r : Role, roleCount s r = (B : ℤ))
    (htree : subclassCount s .tp + subclassCount s .tm = subclassCount s .ft)
    (hanchor : subclassCount s .z = subclassCount s .ft + subclassCount s .fm)
    (hglobal : subclassCount s .up + subclassCount s .um =
      subclassCount s .ft + subclassCount s .fm)
    (hlocal : subclassCount s .dm = subclassCount s .ft + subclassCount s .fm)
    (hminus : subclassCount s .tm = subclassCount s .um) :
    (∑ i, primaryScore (s i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_coefficients
  have hr (r : Role) : (∑ i, primaryCoeff (roleCoeffIndex r) (s i)) = 0 := by
    rw [sum_primaryCoeff_role, hrole, hcard]
    push_cast
    ring
  intro j
  fin_cases j
  · simpa [roleCoeffIndex, Role.index] using hr .x
  · simpa [roleCoeffIndex, Role.index] using hr .anchor
  · simpa [roleCoeffIndex, Role.index] using hr .«global»
  · simpa [roleCoeffIndex, Role.index] using hr .«local»
  · simpa [roleCoeffIndex, Role.index] using hr .flag
  · change (∑ i, primaryCoeff (5 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_five s, htree, sub_self]
  · change (∑ i, primaryCoeff (6 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_six s, hanchor]
    ring
  · change (∑ i, primaryCoeff (7 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_seven s, hglobal]
    ring
  · change (∑ i, primaryCoeff (8 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_eight s, hlocal]
    ring
  · change (∑ i, primaryCoeff (9 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_nine s, hminus, sub_self]

def labelledRoleCount {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n)) (r : Role) (v : Fin n) : ℤ :=
  ∑ i, if (s i).role = r ∧ label i = some v then 1 else 0

theorem sum_secondaryScore_eq {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n)) :
    (∑ i, secondaryScore (s i) (label i)) =
      ∑ v : Fin n, (labelledRoleCount s label .x v -
        2 * labelledRoleCount s label .anchor v +
        labelledRoleCount s label .«local» v) * labelWeight v := by
  classical
  have pointwise (c : Subclass) (l : Option (Fin n)) :
      secondaryScore c l =
        ∑ v : Fin n,
          ((if c.role = Role.x ∧ l = some v then (1 : ℤ) else 0) -
            2 * (if c.role = Role.anchor ∧ l = some v then (1 : ℤ) else 0) +
            (if c.role = Role.«local» ∧ l = some v then (1 : ℤ) else 0)) *
              labelWeight v := by
    cases l with
    | none => cases hc : c.role <;> simp [secondaryScore, hc]
    | some a =>
        cases hc : c.role <;>
          simp [secondaryScore, hc, eq_comm]
  simp_rw [pointwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [labelledRoleCount, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum,
    add_mul, sub_mul, mul_assoc]

theorem sum_secondaryScore_eq_zero_of_inventory {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n))
    (hx : ∀ v, labelledRoleCount s label .x v = labelledRoleCount s label .anchor v)
    (hd : ∀ v, labelledRoleCount s label .«local» v =
      labelledRoleCount s label .anchor v) :
    (∑ i, secondaryScore (s i) (label i)) = 0 := by
  rw [sum_secondaryScore_eq]
  apply Finset.sum_eq_zero
  intro v _
  rw [hx, hd]
  ring

namespace GlobalSpecies

def equivSum (G : GraphInput) :
    GlobalSpecies G ≃ (Bool ⊕ Bool) ⊕ (G.Edge × Bool) where
  toFun
    | .up b => .inl (.inl b)
    | .um b => .inl (.inr b)
    | .edge e b => .inr (e, b)
  invFun
    | .inl (.inl b) => .up b
    | .inl (.inr b) => .um b
    | .inr (e, b) => .edge e b
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with ((b | b) | ⟨e, b⟩) <;> rfl

theorem sum_univ {A : Type*} [AddCommMonoid A] (G : GraphInput)
    (f : GlobalSpecies G → A) :
    (∑ s, f s) = f (.up true) + f (.up false) + f (.um true) + f (.um false) +
      ∑ e : G.Edge, (f (.edge e true) + f (.edge e false)) := by
  calc
    _ = ∑ x : (Bool ⊕ Bool) ⊕ (G.Edge × Bool), f ((equivSum G).symm x) :=
      Fintype.sum_equiv (equivSum G) _ _ (fun _ => by simp)
    _ = _ := by
      simp [equivSum, Fintype.sum_sum_type, Fintype.sum_prod_type,
        add_assoc, add_comm]

end GlobalSpecies

namespace FlagSpecies

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : FlagSpecies → A) :
    (∑ s, f s) = f .tree + f .main + f .edge := by
  have h : (Finset.univ : Finset FlagSpecies) = {.tree, .main, .edge} := by decide
  rw [h]
  simp [add_assoc]

end FlagSpecies

namespace InventoryData

variable (D : InventoryData)

theorem card_treeRow : Fintype.card D.TreeRow = D.t := by
  simp [TreeRow, t, tPlus, tMinus, Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem card_jobCopy (v : D.Vertex) : Fintype.card (D.JobCopy v) = D.J v :=
  D.graph.card_jobCopy D.R D.d v

theorem card_rowAt (v : D.Vertex) : Fintype.card (D.RowAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.TreeRow ⊕ (Bool × D.JobCopy v)) = _
  rw [Fintype.card_sum, D.card_treeRow, Fintype.card_prod, Fintype.card_bool,
    D.card_jobCopy]

theorem card_mBase (v : D.Vertex) : Fintype.card (D.MBase v) = D.t + D.J v := by
  change Fintype.card (D.TreeRow ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_treeRow, D.card_jobCopy]

theorem card_anchorAt (v : D.Vertex) :
    Fintype.card (D.AnchorAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.MBase v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_mBase, D.card_jobCopy]
  omega

theorem card_localBin (v : D.Vertex) :
    Fintype.card (D.LocalBin v) = D.t + 2 * D.J v :=
  D.card_anchorAt v

theorem P_le_t : D.P ≤ D.t := by
  dsimp [t, tPlus, tMinus]
  omega

theorem d_le_tPlus : D.d ≤ D.tPlus := by
  have h := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  simpa [tPlus] using (show D.d ≤ D.d * Fintype.card D.plus.Node + D.P by omega)

theorem d_le_tMinus : D.d ≤ D.tMinus := by
  have h := Nat.mul_le_mul_left D.d (D.minus.node_card_pos)
  simpa [tMinus] using h

theorem two_mul_d_le_t_sub_P : 2 * D.d ≤ D.t - D.P := by
  have hp := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  have hm := D.d_le_tMinus
  dsimp [t, tPlus, tMinus] at *
  omega

theorem card_positiveLocal : Fintype.card D.PositiveLocal = D.P := by
  classical
  simp only [PositiveLocal, Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_coe_sort (Finset.Icc 1 D.L) D.quota

theorem card_zeroLocalAt (v : D.Vertex) :
    Fintype.card (D.ZeroLocalAt v) = D.t + D.J v - D.P := by
  simp only [ZeroLocalAt, Fintype.card_sum, Fintype.card_fin, card_jobCopy]
  have h := D.P_le_t
  omega

theorem card_dmAt (v : D.Vertex) : Fintype.card (D.DMAt v) = D.t + D.J v := by
  change Fintype.card (D.PositiveLocal ⊕ D.ZeroLocalAt v) = _
  rw [Fintype.card_sum, D.card_positiveLocal, D.card_zeroLocalAt]
  have h := D.P_le_t
  omega

theorem card_localAt (v : D.Vertex) : Fintype.card (D.LocalAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.DMAt v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_dmAt, D.card_jobCopy]
  omega

theorem sum_J : (∑ v : D.Vertex, D.J v) = 2 * D.d * D.graph.edges.length * D.R := by
  simpa only [D.card_jobCopy] using D.graph.sum_card_jobCopy D.R D.d

theorem plusSlots_eq : D.plusSlots = D.graph.n * D.tPlus + ∑ v : D.Vertex, D.J v := by
  simp [plusSlots, Finset.sum_add_distrib, Finset.sum_const]

theorem B_eq : D.B = D.graph.n * D.t + 2 * ∑ v : D.Vertex, D.J v := by
  simp [B, Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum]

theorem B_closed : D.B = D.graph.n * D.t + 4 * D.d * D.graph.edges.length * D.R := by
  rw [B_eq, sum_J]
  ring

theorem unitPlus_le_stock (hk : D.k ≤ D.graph.n) : D.d * D.k ≤ D.plusSlots := by
  calc
    D.d * D.k ≤ D.d * D.graph.n := Nat.mul_le_mul_left D.d hk
    _ ≤ D.graph.n * D.tPlus := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left D.graph.n D.d_le_tPlus
    _ ≤ D.plusSlots := by rw [plusSlots_eq]; omega

theorem unitMinus_le_stock : D.d * (D.graph.n - D.k) ≤ D.minusSlots := by
  calc
    D.d * (D.graph.n - D.k) ≤ D.d * D.graph.n :=
      Nat.mul_le_mul_left D.d (Nat.sub_le _ _)
    _ ≤ D.minusSlots := by
      simpa [minusSlots, Nat.mul_comm] using
        Nat.mul_le_mul_left D.graph.n D.d_le_tMinus

theorem up_species_total (hk : D.k ≤ D.graph.n) :
    D.globalStock (.up true) + D.globalStock (.up false) = D.plusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le (D.unitPlus_le_stock hk)

theorem um_species_total :
    D.globalStock (.um true) + D.globalStock (.um false) = D.minusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le D.unitMinus_le_stock

theorem card_globalCopy (hk : D.k ≤ D.graph.n) : Fintype.card D.GlobalCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [GlobalSpecies.sum_univ]
  rw [D.up_species_total hk]
  rw [show D.plusSlots + D.globalStock (.um true) + D.globalStock (.um false) =
    D.plusSlots + D.minusSlots by rw [Nat.add_assoc, D.um_species_total]]
  simp only [globalStock, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [D.plusSlots_eq, D.B_eq, D.sum_J]
  dsimp [minusSlots, t]
  ring

theorem card_flagCopy : Fintype.card D.FlagCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [FlagSpecies.sum_univ]
  dsimp [flagStock, treeFlags, jobFlags]
  rw [D.B_eq]
  ring

theorem card_roleCopies (hk : D.k ≤ D.graph.n) (r : Role) :
    Fintype.card (D.RoleCopies r) = D.B := by
  cases r with
  | x => simp [RoleCopies, Fintype.card_sigma, D.card_rowAt, B]
  | anchor => simp [RoleCopies, Fintype.card_sigma, D.card_anchorAt, B]
  | «global» => exact D.card_globalCopy hk
  | «local» => simp [RoleCopies, Fintype.card_sigma, D.card_localAt, B]
  | flag => exact D.card_flagCopy

theorem card_item (hk : D.k ≤ D.graph.n) : Fintype.card D.Item = 5 * D.B := by
  rw [Fintype.card_sigma, Role.sum_univ]
  simp only [D.card_roleCopies hk]
  omega

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def allJobEquiv : (Σ v : D.Vertex, D.JobCopy v) ≃
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d where
  toFun j := ((j.2.1.1.val, j.2.1.2), j.2.2)
  invFun j := ⟨D.graph.endpoint j.1.1.1 j.1.1.2,
    ((⟨j.1.1, rfl⟩, j.1.2), j.2)⟩
  left_inv := by
    rintro ⟨v, ⟨⟨⟨es, hv⟩, rep⟩, copy⟩⟩
    cases hv
    rfl
  right_inv := by rintro ⟨⟨⟨edge, side⟩, rep⟩, copy⟩; rfl

def keyItem (j : Σ v : D.Vertex, D.JobCopy v) : D.Item :=
  ⟨.anchor, ⟨j.1, .inr j.2⟩⟩

def keyData : D.Item → Option (Σ v : D.Vertex, D.JobCopy v)
  | ⟨.anchor, ⟨v, .inr j⟩⟩ => some ⟨v, j⟩
  | _ => none

@[simp] theorem keyData_keyItem (j : Σ v : D.Vertex, D.JobCopy v) :
    D.keyData (D.keyItem j) = some j := by cases j; rfl

theorem keyItem_injective : Function.Injective D.keyItem := by
  intro i j h
  exact Option.some.inj (by simpa only [D.keyData_keyItem] using congrArg D.keyData h)

@[simp] theorem keyItem_role (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemRole (D.keyItem j) = .anchor := rfl

@[simp] theorem keyItem_subclass (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemSubclass (D.keyItem j) = .y := rfl

@[simp] theorem keyItem_label (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemLabel (D.keyItem j) = some j.1 := rfl

def edgeResourceItem (w : (D.Edge × Bool) × Fin (D.d * D.R)) : D.Item :=
  ⟨.«global», ⟨.edge w.1.1 w.1.2, w.2⟩⟩

def edgeResourceData : D.Item → Option ((D.Edge × Bool) × Fin (D.d * D.R))
  | ⟨.«global», ⟨.edge e permit, copy⟩⟩ => some ((e, permit), copy)
  | _ => none

@[simp] theorem edgeResourceData_edgeResourceItem
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.edgeResourceData (D.edgeResourceItem w) = some w := by cases w; rfl

theorem edgeResourceItem_injective : Function.Injective D.edgeResourceItem := by
  intro i j h
  exact Option.some.inj (by
    simpa only [D.edgeResourceData_edgeResourceItem] using congrArg D.edgeResourceData h)

def prefixJobIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d) :
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d :=
  ((⟨⟨j.1.1.1.val, lt_of_lt_of_le j.1.1.1.isLt hle⟩, j.1.1.2⟩, j.1.2), j.2)

theorem prefixJobIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixJobIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun x => x.1.1.1.val) hij
      · exact congrArg (fun x => x.1.1.2) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : ((D.Edge × Fin 2) × Fin D.R) × Fin D.d => x.2) hij

def earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun j => D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))

theorem earlierKeys_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeys h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d =>
      D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))) := by
    intro i j hij
    exact D.prefixJobIndex_injective h hle
      (D.allJobEquiv.symm.injective (D.keyItem_injective hij))
  rw [earlierKeys, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

theorem mem_earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierKeys h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.keyItem j = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.allJobEquiv.symm (D.prefixJobIndex h hle j), rfl, j.1.1.1.isLt⟩
  · rintro ⟨j, rfl, hj⟩
    let a := D.allJobEquiv j
    let x : ((Fin h × Fin 2) × Fin D.R) × Fin D.d :=
      ((⟨⟨a.1.1.1.val, hj⟩, a.1.1.2⟩, a.1.2), a.2)
    have hx : D.prefixJobIndex h hle x = a := by
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Fin.ext; rfl
          · rfl
        · rfl
      · rfl
    refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
    rw [hx]
    exact congrArg D.keyItem (D.allJobEquiv.symm_apply_apply j)

def prefixWIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (Fin h × Bool) × Fin (D.d * D.R)) :
    (D.Edge × Bool) × Fin (D.d * D.R) :=
  ((⟨w.1.1.val, lt_of_lt_of_le w.1.1.isLt hle⟩, w.1.2), w.2)

theorem prefixWIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixWIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x => x.1.1.val) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : (D.Edge × Bool) × Fin (D.d * D.R) => x.2) hij

def earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun w => D.edgeResourceItem (D.prefixWIndex h hle w)

theorem earlierW_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierW h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun w : (Fin h × Bool) × Fin (D.d * D.R) =>
      D.edgeResourceItem (D.prefixWIndex h hle w)) := by
    intro i j hij
    exact D.prefixWIndex_injective h hle (D.edgeResourceItem_injective hij)
  rw [earlierW, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem mem_earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierW h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.edgeResourceItem w = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.prefixWIndex h hle w, rfl, w.1.1.isLt⟩
  · rintro ⟨w, rfl, hw⟩
    let x : (Fin h × Bool) × Fin (D.d * D.R) :=
      ((⟨w.1.1.val, hw⟩, w.1.2), w.2)
    have hx : D.prefixWIndex h hle x = w := by
      apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext; rfl
        · rfl
      · rfl
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, congrArg D.edgeResourceItem hx⟩

theorem earlierW_card_eq_keys (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierW h hle).card = (D.earlierKeys h hle).card := by
  rw [D.earlierW_card, D.earlierKeys_card]

end InventoryData
end BinPackingGap

end

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

private theorem subclassCount_by_role (subclass : Subclass) :
    subclassCount D.itemSubclass subclass =
      ∑ i : D.RoleCopies subclass.role,
        subclassIndicator (D.itemSubclass ⟨subclass.role, i⟩) subclass := by
  classical
  unfold subclassCount
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_single subclass.role ?_ ?_
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro hi
    apply hr
    calc
      r = (D.itemSubclass ⟨r, i⟩).role := (D.itemSubclass_role ⟨r, i⟩).symm
      _ = subclass.role := congrArg Subclass.role hi
  · simp

theorem roleCount_itemSubclass (hk : D.k ≤ D.graph.n) (r : Role) :
    roleCount D.itemSubclass r = (D.B : ℤ) := by
  classical
  simp only [roleCount, D.itemSubclass_role, itemRole, Fintype.sum_sigma]
  have hrole : (∑ s : Role, ∑ _ : D.RoleCopies s,
      if s = r then (1 : ℤ) else 0) = (Fintype.card (D.RoleCopies r) : ℤ) := by
    simp
  rw [hrole, D.card_roleCopies hk]

theorem subclassCount_tp :
    subclassCount D.itemSubclass .tp = D.graph.n * (D.tPlus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tp) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tPlus, Nat.cast_add, Nat.cast_mul, mul_add,
    mul_comm, mul_left_comm]

theorem subclassCount_tm :
    subclassCount D.itemSubclass .tm = D.graph.n * (D.tMinus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tMinus, Nat.cast_mul, mul_comm, mul_left_comm]

theorem subclassCount_s :
    subclassCount D.itemSubclass .s = 2 * ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .s) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy, Finset.mul_sum, mul_comm]

theorem subclassCount_z :
    subclassCount D.itemSubclass .z = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.AnchorAt v), subclassIndicator (D.itemSubclass ⟨.anchor, i⟩) .z) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_mBase]

theorem subclassCount_y :
    subclassCount D.itemSubclass .y = ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.AnchorAt v), subclassIndicator (D.itemSubclass ⟨.anchor, i⟩) .y) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy]

theorem subclassCount_up (hk : D.k ≤ D.graph.n) :
    subclassCount D.itemSubclass .up = (D.plusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .up) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) (D.up_species_total hk)
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_um :
    subclassCount D.itemSubclass .um = (D.minusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .um) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) D.um_species_total
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_dm :
    subclassCount D.itemSubclass .dm = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.LocalAt v), subclassIndicator (D.itemSubclass ⟨.«local», i⟩) .dm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_dmAt]

theorem subclassCount_dg :
    subclassCount D.itemSubclass .dg = ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.LocalAt v), subclassIndicator (D.itemSubclass ⟨.«local», i⟩) .dg) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy]

theorem subclassCount_ft :
    subclassCount D.itemSubclass .ft = (D.treeFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .ft) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.treeFlags) = D.treeFlags
  exact Fintype.card_fin _

theorem subclassCount_fm :
    subclassCount D.itemSubclass .fm = (D.jobFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .fm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.jobFlags) = D.jobFlags
  exact Fintype.card_fin _

theorem subclassCount_fg :
    subclassCount D.itemSubclass .fg = (D.jobFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .fg) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.jobFlags) = D.jobFlags
  exact Fintype.card_fin _

theorem total_primaryScore_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.Item, primaryScore (D.itemSubclass i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_inventory D.itemSubclass D.B
    (D.card_item hk) (D.roleCount_itemSubclass hk)
  · rw [D.subclassCount_tp, D.subclassCount_tm, D.subclassCount_ft]
    simp [treeFlags, t, Nat.cast_mul, Nat.cast_add, mul_add]
  · rw [D.subclassCount_z, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_up hk, D.subclassCount_um, D.subclassCount_ft,
      D.subclassCount_fm, D.plusSlots_eq]
    simp [minusSlots, treeFlags, jobFlags, t, Nat.cast_mul, Nat.cast_add,
      Nat.cast_sum, mul_add]
    ring
  · rw [D.subclassCount_dm, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_tm, D.subclassCount_um]
    simp [minusSlots]

theorem labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_rowAt]

theorem labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_anchorAt]

theorem labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_localAt]

theorem total_secondaryScore_eq_zero :
    (∑ i : D.Item, secondaryScore (D.itemSubclass i) (D.itemLabel i)) = 0 := by
  apply sum_secondaryScore_eq_zero_of_inventory D.itemSubclass D.itemLabel
  · intro v
    rw [D.labelledRoleCount_x, D.labelledRoleCount_anchor]
  · intro v
    rw [D.labelledRoleCount_local, D.labelledRoleCount_anchor]

end InventoryData

end BinPackingGap

end OAI
