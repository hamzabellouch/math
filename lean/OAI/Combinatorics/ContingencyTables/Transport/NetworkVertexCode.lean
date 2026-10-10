import OAI.Combinatorics.ContingencyTables.Transport.BoundedTableFeasibility
import OAI.Combinatorics.ContingencyTables.Machines.ResidualGraphProgram

namespace OAI

/-! # Explicit source/row/column/sink indices for the executed network -/

namespace ContingencyTables.NetworkVertexCode

open LayeredTableNetwork ResidualGraphProgram

variable {m n : ℕ}

/-- Source and sink occupy zero and one, then rows and columns. -/
def index : Vertex m n→ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr (.inl i) => 2+i.val
  | .inr (.inr j) => 2+m+j.val

def tag : Vertex m n→ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 3

def kind (m k : ℕ) : ℕ :=
  if k=0 then 0 else if k=1 then 1 else if k<2+m then 2 else 3

lemma kind_index (v : Vertex m n) : kind m (index v)=tag v := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · have h0 : 2+i.val≠0 := by omega
    have h1 : 2+i.val≠1 := by omega
    have h2 : 2+i.val<2+m := by have hi := i.isLt; omega
    simp only [index,tag,kind,h0,h1,h2,ite_false,ite_true]
  · have h0 : 2+m+j.val≠0 := by omega
    have h1 : 2+m+j.val≠1 := by omega
    have h2 : ¬2+m+j.val<2+m := by omega
    simp only [index,tag,kind,h0,h1,h2,ite_false]

lemma index_vertices (v : Vertex m n) :
    (BoundedTableFeasibility.vertices m n v).val=index v := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · simp [BoundedTableFeasibility.vertices,index,finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
  · simp [BoundedTableFeasibility.vertices,index,
      finSumFinEquiv_apply_right,Nat.add_assoc]

abbrev Input := (List ℕ×List ℕ)×NatMatrix

def entry (z : Input×(ℕ×ℕ)) : ℕ :=
  let ku := kind z.1.1.1.length z.2.1
  let kv := kind z.1.1.1.length z.2.2
  if ku=0 ∧ kv=2 then z.1.1.1.getD (z.2.2-2) 0
  else if ku=2 ∧ kv=3 then capacityEntry (z.1.2,(z.2.1-2,z.2.2-(2+z.1.1.1.length)))
  else if ku=3 ∧ kv=1 then z.1.1.2.getD (z.2.1-(2+z.1.1.1.length)) 0
  else 0

def data (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) : Input :=
  ((List.ofFn r,List.ofFn c),natCode b)

lemma entry_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (u v : Vertex m n) :
    entry (data r c b,(index u,index v))=capacity r c b u v := by
  have he : (data r c b).1.1.length=m := by simp [data]
  have hcol (k : ℕ) : 2+(m+k)-(2+m)=k := by omega
  simp only [entry,he,kind_index]
  rcases u with a | (i | j) <;> rcases v with d | (k | l)
  all_goals (try cases a) <;> (try cases d)
  all_goals simp [tag,index,data,capacity,capacityEntry,natCode,
    List.getD_eq_getElem?_getD,
    Nat.add_assoc,hcol]

def vertexCount (z : Input) : ℕ := 2+(z.1.1.length+z.1.2.length)

def matrix (z : Input) : NatMatrix :=
  (List.range (vertexCount z)).map (fun u=>
    (List.range (vertexCount z)).map (fun v=>entry (z,(u,v))))

lemma matrix_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    matrix (data r c b)=natCode (BoundedTableFeasibility.networkCapacity r c b) := by
  have hn : vertexCount (data r c b)=2+(m+n) := by simp [vertexCount,data]
  simp only [matrix,hn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have hu : u.val=index ((BoundedTableFeasibility.vertices m n).symm u) := by
    rw [←index_vertices,Equiv.apply_symm_apply]
  have hv : v.val=index ((BoundedTableFeasibility.vertices m n).symm v) := by
    rw [←index_vertices,Equiv.apply_symm_apply]
  simp only [Function.comp_apply,hu,hv]
  exact entry_code r c b _ _

end ContingencyTables.NetworkVertexCode

end OAI
