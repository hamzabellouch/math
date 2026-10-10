import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace CompanionFPP

variable {V : Type*} {G : SimpleGraph V}

abbrev Weights (G : SimpleGraph V) := G.edgeSet → ℝ

def edgeCost (w : Weights G) {x y : V} (h : G.Adj x y) : ℝ :=
  w ⟨s(x, y), h⟩

@[simp] theorem edgeCost_symm (w : Weights G) {x y : V} (h : G.Adj x y) :
    edgeCost w h.symm = edgeCost w h := by
  simp only [edgeCost, Sym2.eq_swap]

def pathCost (w : Weights G) {x y : V} : G.Walk x y → ℝ
  | .nil => 0
  | .cons h p => edgeCost w h + pathCost w p

@[simp] theorem pathCost_nil (w : Weights G) (x : V) :
    pathCost w (SimpleGraph.Walk.nil : G.Walk x x) = 0 := rfl

@[simp] theorem pathCost_cons (w : Weights G) {x y z : V}
    (h : G.Adj x y) (p : G.Walk y z) :
    pathCost w (.cons h p) = edgeCost w h + pathCost w p := rfl

@[simp] theorem pathCost_append (w : Weights G) {x y z : V}
    (p : G.Walk x y) (q : G.Walk y z) :
    pathCost w (p.append q) = pathCost w p + pathCost w q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

theorem pathCost_nonneg (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : 0 ≤ pathCost w p := by
  induction p with
  | nil => exact le_refl 0
  | cons h p ih => exact add_nonneg (hw _) ih

noncomputable def passageTime (w : Weights G) (x y : V) : ℝ :=
  sInf (Set.range (fun p : G.Walk x y => pathCost w p))

theorem passageTime_le_pathCost (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : passageTime w x y ≤ pathCost w p := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨q, rfl⟩; exact pathCost_nonneg w hw q⟩
  · exact ⟨p, rfl⟩

@[simp] theorem pathCost_reverse (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p.reverse = pathCost w p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp [SimpleGraph.Walk.reverse_cons, ih, edgeCost, Sym2.eq_swap, add_comm]

theorem passageTime_nonneg (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (hp : Nonempty (G.Walk x y)) : 0 ≤ passageTime w x y := by
  obtain ⟨p⟩ := hp
  apply le_csInf (s := Set.range (fun p : G.Walk x y => pathCost w p)) ⟨_, ⟨p, rfl⟩⟩
  rintro _ ⟨q, rfl⟩
  exact pathCost_nonneg w hw q

@[simp] theorem passageTime_self (w : Weights G) (hw : ∀ e, 0 ≤ w e) (x : V) :
    passageTime w x x = 0 := by
  apply le_antisymm
  · simpa using passageTime_le_pathCost w hw (SimpleGraph.Walk.nil : G.Walk x x)
  · exact passageTime_nonneg w hw ⟨.nil⟩

theorem passageTime_symm (w : Weights G) (x y : V) :
    passageTime w x y = passageTime w y x := by
  unfold passageTime
  congr 1
  ext t
  constructor <;> rintro ⟨p, rfl⟩ <;> exact ⟨p.reverse, pathCost_reverse w p⟩

theorem passageTime_triangle (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y z : V} (hxy : Nonempty (G.Walk x y)) (hyz : Nonempty (G.Walk y z)) :
    passageTime w x z ≤ passageTime w x y + passageTime w y z := by
  obtain ⟨p₀⟩ := hxy
  obtain ⟨q₀⟩ := hyz
  suffices h : passageTime w x z - passageTime w x y ≤ passageTime w y z by linarith
  apply le_csInf (s := Set.range (fun q : G.Walk y z => pathCost w q)) ⟨_, ⟨q₀, rfl⟩⟩
  rintro _ ⟨q, rfl⟩
  suffices h : passageTime w x z - pathCost w q ≤ passageTime w x y by linarith
  apply le_csInf (s := Set.range (fun p : G.Walk x y => pathCost w p)) ⟨_, ⟨p₀, rfl⟩⟩
  rintro _ ⟨p, rfl⟩
  have h := passageTime_le_pathCost w hw (p.append q)
  rw [pathCost_append] at h
  linarith

structure Calibration (w : Weights G) where
  B : V → V → ℝ
  additive : ∀ x y z, B x z = B x y + B y z
  edge_le : ∀ {x y}, (h : G.Adj x y) → B x y ≤ edgeCost w h

namespace Calibration
variable {w : Weights G} (b : Calibration w)

@[simp] theorem self (x : V) : b.B x x = 0 := by
  have h := b.additive x x x
  linarith

@[simp] theorem reverse (x y : V) : b.B y x = -b.B x y := by
  have h := b.additive x y x
  rw [b.self] at h
  linarith

theorem le_pathCost {x y : V} (p : G.Walk x y) : b.B x y ≤ pathCost w p := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    rw [pathCost_cons, b.additive x y z]
    exact add_le_add (b.edge_le h) ih

def defect {x y : V} (p : G.Walk x y) := pathCost w p - b.B x y

theorem defect_nonneg {x y : V} (p : G.Walk x y) : 0 ≤ b.defect p :=
  sub_nonneg.mpr (b.le_pathCost p)

theorem defect_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    b.defect (p.append q) = b.defect p + b.defect q := by
  simp only [defect, pathCost_append, b.additive x y z]
  ring

theorem defect_subpath_le {a x y z : V} (p : G.Walk a x)
    (q : G.Walk x y) (r : G.Walk y z) :
    b.defect q ≤ b.defect ((p.append q).append r) := by
  rw [b.defect_append, b.defect_append]
  have := b.defect_nonneg p
  have := b.defect_nonneg r
  linarith

theorem defect_eq_centered (o : V) (h : V → ℝ) {x y : V} (p : G.Walk x y) :
    b.defect p = (pathCost w p - (h y - h x)) -
      (b.B o y - h y) + (b.B o x - h x) := by
  have := b.additive o x y
  unfold defect
  linarith

end Calibration

end CompanionFPP

end OAI
