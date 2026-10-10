import OAI.Combinatorics.PolynomialVacuum.Cylinder.Repeat
import OAI.Combinatorics.HoneycombCorridor.StripWindows

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumBridge.Corridor

def layer : PlaneVertex → ℤ
  | .up _ j => j
  | .down _ j => j

def horizontal : PlaneVertex → ℤ
  | .up i _ => i
  | .down i _ => i

noncomputable def aboveBox (A : ℤ) (R : ℕ) : Finset PlaneVertex :=
  ((Finset.Icc (-(R : ℤ)) R).product (Finset.Icc A (A+R))).biUnion fun p =>
    {PolynomialVacuumBridge.Corridor.Vertex.up p.1 p.2,PolynomialVacuumBridge.Corridor.Vertex.down p.1 p.2}

theorem mem_aboveBox (A : ℤ) (R : ℕ) (v : PlaneVertex) : v∈aboveBox A R ↔
    -(R : ℤ)≤horizontal v ∧ horizontal v≤R ∧ A≤layer v ∧ layer v≤A+R := by
  cases v <;> simp [aboveBox,Finset.mem_biUnion,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton,horizontal,layer] <;> aesop

theorem aboveBox_convex (A : ℤ) (R : ℕ) : AdmissiblyConvex (aboveBox A R) := by
  apply admissiblyConvex_of_box _
    (fun k => if k=0 then A else if k=1 then -(R : ℤ) else A-R)
    (fun k => if k=0 then A+R+1 else if k=1 then R+1 else A+2*R+2)
  intro v
  rw [mem_aboveBox]
  cases v <;> simp only [horizontal,layer]
  all_goals constructor
  all_goals
    first
    | (rintro ⟨hi,hi',hj,hj'⟩ k; fin_cases k <;> simp [boxIndex] <;> omega)
    | (intro h; have h0 := h 0; have h1 := h 1; simp [boxIndex] at h0 h1; omega)

theorem finite_above_box (A : ℤ) (S : Finset PlaneVertex) (h : ∀ v∈S, A≤layer v) :
    ∃ R : ℕ, S⊆aboveBox A R := by
  let R := S.sup (fun v => max (horizontal v).natAbs (layer v-A).natAbs)
  refine ⟨R,?_⟩
  intro v hv
  have hb := Finset.le_sup (f:=fun v => max (horizontal v).natAbs (layer v-A).natAbs) hv
  have hi : (horizontal v).natAbs≤R := (le_max_left _ _).trans hb
  have hj : (layer v-A).natAbs≤R := (le_max_right _ _).trans hb
  have hi' : |horizontal v|≤(R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hi
  have hj' : |layer v-A|≤(R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hj
  exact (mem_aboveBox A R v).mpr ⟨(abs_le.mp hi').1,(abs_le.mp hi').2,h v hv,by omega⟩

@[simp] theorem layer_translate (d : ℤ) (v : PlaneVertex) : layer (translateVertex d v)=layer v := by
  cases v <;> rfl

end PolynomialVacuumCylinder

end OAI
