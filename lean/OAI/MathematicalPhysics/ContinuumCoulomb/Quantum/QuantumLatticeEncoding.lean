import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeSerialization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeSource
import Mathlib.Data.List.OfFn

namespace OAI

/-! Finite source objects serialize to valid binary instances with canonical
rational coefficients and the same physical sites and thresholds. -/

namespace ContinuumCoulomb.SquareLatticeHeisenberg

def binaryEdge (d : SquareLatticeHeisenberg) (i : Fin d.edges) : BinaryHeisenbergEdge :=
  ⟨d.left i,d.right i,BinaryRational.ofRat (d.coefficient i)⟩

def binary (d : SquareLatticeHeisenberg) : BinaryHeisenberg where
  coordinate := List.ofFn d.coordinate
  edges := List.ofFn d.binaryEdge
  lower := BinaryRational.ofRat d.lower
  upper := BinaryRational.ofRat d.upper

@[simp] theorem binary_vertices (d : SquareLatticeHeisenberg) : d.binary.coordinate.length = d.vertices :=
  List.length_ofFn
@[simp] theorem binary_edges (d : SquareLatticeHeisenberg) : d.binary.edges.length = d.edges :=
  List.length_ofFn

private theorem get_ofFn_value {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).get ⟨i,by simpa using hi⟩ = f ⟨i,hi⟩ := by
  simp [List.get_eq_getElem]

theorem binary_getEdge (d : SquareLatticeHeisenberg) (i : Fin d.binary.edges.length) :
    d.binary.edges.get i = d.binaryEdge ⟨i.val,by simpa using i.isLt⟩ := by
  exact get_ofFn_value d.binaryEdge i.val (by simpa using i.isLt)

theorem binary_getCoordinate (d : SquareLatticeHeisenberg) (i : Fin d.vertices) :
    d.binary.coordinate.getD i.val (0,0) = d.coordinate i := by
  rw [List.getD_eq_get _ _ ⟨i.val,by rw [binary_vertices]; exact i.isLt⟩]
  simp only [binary,List.get_ofFn]
  rfl

theorem binary_valid (d : SquareLatticeHeisenberg) : d.binary.Valid := by
  constructor
  · simpa using d.vertices_pos
  · exact List.nodup_ofFn.mpr d.coordinate_injective
  · intro e
    rw [d.binary_getEdge e]
    simpa only [binaryEdge,binary_vertices] using
      And.intro (d.left ⟨e.val,by simpa using e.isLt⟩).isLt
        (d.right ⟨e.val,by simpa using e.isLt⟩).isLt
  · intro e
    rw [d.binary_getEdge e]
    exact (d.coefficient _).den_pos
  · intro e
    rw [d.binary_getEdge e]
    simp only [binaryEdge,d.binary_getCoordinate]
    exact d.adjacent _
  · intro e f hef
    rw [d.binary_getEdge e,d.binary_getEdge f]
    let e' : Fin d.edges := ⟨e.val,by simpa using e.isLt⟩
    let f' : Fin d.edges := ⟨f.val,by simpa using f.isLt⟩
    have hne : e' ≠ f' := by
      intro h
      apply hef
      have hv : e.val = f.val := congrArg (fun z : Fin d.edges => z.val) h
      exact Fin.ext hv
    have hs := d.edge_simple e' f' hne
    constructor
    · rintro ⟨hl,hr⟩
      exact hs.1 ⟨Fin.ext hl,Fin.ext hr⟩
    · rintro ⟨hl,hr⟩
      exact hs.2 ⟨Fin.ext hl,Fin.ext hr⟩
  · exact d.lower.den_pos
  · exact d.upper.den_pos
  · simpa only [binary,BinaryRational.value_ofRat] using d.gap_pos

@[simp] theorem binary_lower (d : SquareLatticeHeisenberg) : d.binary.lower.value = d.lower :=
  BinaryRational.value_ofRat _
@[simp] theorem binary_upper (d : SquareLatticeHeisenberg) : d.binary.upper.value = d.upper :=
  BinaryRational.value_ofRat _

private theorem ext_data {d e : SquareLatticeHeisenberg}
    (hn : d.vertices = e.vertices) (hc : HEq d.coordinate e.coordinate)
    (hm : d.edges = e.edges) (hl : HEq d.left e.left) (hr : HEq d.right e.right)
    (hJ : HEq d.coefficient e.coefficient) (ha : d.lower = e.lower) (hb : d.upper = e.upper) : d = e := by
  cases d
  cases e
  cases hn
  cases hm
  cases hc
  cases hl
  cases hr
  cases hJ
  cases ha
  cases hb
  rfl

theorem binary_toSource (d : SquareLatticeHeisenberg) :
    d.binary.toSource d.binary_valid = d := by
  apply ext_data (d.binary_vertices) ?_ (d.binary_edges) ?_ ?_ ?_ (binary_lower d) (binary_upper d)
  · apply (Fin.heq_fun_iff d.binary_vertices).mpr
    intro i
    exact get_ofFn_value d.coordinate i.val (by simpa using i.isLt)
  · apply Function.hfunext (congrArg Fin d.binary_edges)
    intro i j hij
    apply (Fin.heq_ext_iff d.binary_vertices).mpr
    change (d.binary.edges.get i).left = (d.left j).val
    rw [d.binary_getEdge i]
    dsimp only [binaryEdge]
    have hval := Fin.val_eq_val_of_heq hij
    exact congrArg (fun e : Fin d.edges => (d.left e).val) (Fin.ext hval)
  · apply Function.hfunext (congrArg Fin d.binary_edges)
    intro i j hij
    apply (Fin.heq_ext_iff d.binary_vertices).mpr
    change (d.binary.edges.get i).right = (d.right j).val
    rw [d.binary_getEdge i]
    dsimp only [binaryEdge]
    have hval := Fin.val_eq_val_of_heq hij
    exact congrArg (fun e : Fin d.edges => (d.right e).val) (Fin.ext hval)
  · apply (Fin.heq_fun_iff d.binary_edges).mpr
    intro i
    change (d.binary.edges.get i).coefficient.value = _
    rw [d.binary_getEdge i]
    exact BinaryRational.value_ofRat _

end ContinuumCoulomb.SquareLatticeHeisenberg

end OAI
