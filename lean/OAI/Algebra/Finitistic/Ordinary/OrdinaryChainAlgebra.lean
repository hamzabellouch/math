import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.Ring

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- The radical-square-zero chain algebra, in vertex and arrow coordinates.
Arrow i goes from i to i+1, with the manuscript's right-projective convention. -/
def ChainAlgebra := (Fin (l+1) → k) × (Fin l → k)
namespace ChainAlgebra
instance : AddCommGroup (ChainAlgebra k l) :=
  inferInstanceAs (AddCommGroup ((Fin (l+1) → k) × (Fin l → k)))
instance : Module k (ChainAlgebra k l) :=
  inferInstanceAs (Module k ((Fin (l+1) → k) × (Fin l → k)))
instance : FiniteDimensional k (ChainAlgebra k l) :=
  inferInstanceAs (FiniteDimensional k ((Fin (l+1) → k) × (Fin l → k)))

@[simp] theorem zero_eq : (0 : ChainAlgebra k l) = (0,0) := rfl
@[simp] theorem add_eq (x y : ChainAlgebra k l) : x+y = (x.1+y.1,x.2+y.2) := rfl
@[simp] theorem smul_eq (c : k) (x : ChainAlgebra k l) : c • x = (c • x.1,c • x.2) := rfl

def diagonal (x : ChainAlgebra k l) := x.1
def radical (x : ChainAlgebra k l) := x.2

def mul (x y : ChainAlgebra k l) : ChainAlgebra k l :=
  (fun i => x.1 i * y.1 i,
   fun i => x.1 i.succ * y.2 i + x.2 i * y.1 i.castSucc)
def unit : ChainAlgebra k l := (fun _ => 1, fun _ => 0)

instance : Ring (ChainAlgebra k l) where
  __ := (inferInstance : AddCommGroup (ChainAlgebra k l))
  mul := mul k l
  one := unit k l
  mul_assoc x y z := by
    change mul k l (mul k l x y) z = mul k l x (mul k l y z)
    apply Prod.ext <;> funext i <;> simp only [mul] <;> ring
  one_mul x := by
    change mul k l (unit k l) x = x
    apply Prod.ext <;> funext i <;> simp [mul, unit]
  mul_one x := by
    change mul k l x (unit k l) = x
    apply Prod.ext <;> funext i <;> simp [mul, unit]
  left_distrib x y z := by
    change mul k l x (y+z) = mul k l x y + mul k l x z
    rw [add_eq k l (mul k l x y) (mul k l x z), add_eq k l y z]
    apply Prod.ext <;> funext i <;> simp only [mul, Pi.add_apply] <;> ring
  right_distrib x y z := by
    change mul k l (x+y) z = mul k l x z + mul k l y z
    rw [add_eq k l (mul k l x z) (mul k l y z), add_eq k l x y]
    apply Prod.ext <;> funext i <;> simp only [mul, Pi.add_apply] <;> ring
  zero_mul x := by
    change mul k l 0 x = 0
    apply Prod.ext <;> funext i <;> simp [mul, zero_eq]
  mul_zero x := by
    change mul k l x 0 = 0
    apply Prod.ext <;> funext i <;> simp [mul, zero_eq]

instance : Algebra k (ChainAlgebra k l) where
  algebraMap :=
    { toFun := fun c => (fun _ => c, fun _ => 0)
      map_one' := rfl
      map_mul' := by
        intro x y
        change ( ((fun _ => x*y), (0 : Fin l → k)) : ChainAlgebra k l) = mul k l (fun _ => x, 0) (fun _ => y, 0)
        apply Prod.ext <;> funext i <;> simp [mul]
      map_zero' := rfl
      map_add' := by
        intro x y
        change ((fun _ => x+y), (0 : Fin l → k)) = ((fun _ => x)+(fun _ => y), (0 : Fin l → k)+(0 : Fin l → k))
        apply Prod.ext <;> funext i <;> simp }
  commutes' c x := by
    apply Prod.ext <;> funext i
    · exact mul_comm c (x.1 i)
    · change c * x.2 i + 0 * x.1 i.castSucc = x.1 i.succ * 0 + x.2 i * c
      ring
  smul_def' c x := by
    apply Prod.ext <;> funext i
    · rfl
    · change c * x.2 i = c * x.2 i + 0 * x.1 i.castSucc
      ring

@[simp] theorem mul_diagonal (x y : ChainAlgebra k l) (i : Fin (l+1)) :
    (x*y).1 i = x.1 i * y.1 i := rfl
@[simp] theorem mul_radical (x y : ChainAlgebra k l) (i : Fin l) :
    (x*y).2 i = x.1 i.succ * y.2 i + x.2 i * y.1 i.castSucc := rfl

def vertex (i : Fin (l+1)) : ChainAlgebra k l := (Pi.single i 1, 0)
def arrow (i : Fin l) : ChainAlgebra k l := (0, Pi.single i 1)

@[simp] theorem vertex_idempotent (i : Fin (l+1)) :
    vertex k l i * vertex k l i = vertex k l i := by
  apply Prod.ext <;> funext j
  · change ((Pi.single i 1 : _ → k) j) * ((Pi.single i 1 : _ → k) j) = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h]
  · change (mul k l (vertex k l i) (vertex k l i)).2 j = 0
    simp [mul, vertex]

@[simp] theorem arrow_mul_arrow (i j : Fin l) :
    arrow k l i * arrow k l j = 0 := by
  change mul k l (arrow k l i) (arrow k l j) = 0
  apply Prod.ext <;> funext a <;> simp [mul, arrow, zero_eq]

@[simp] theorem vertex_target_arrow (i : Fin l) :
    vertex k l i.succ * arrow k l i = arrow k l i := by
  apply Prod.ext <;> funext j
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j * 0 = 0
    simp
  · change (Pi.single i.succ 1 : _ → k) j.succ * (Pi.single i 1 : _ → k) j + 0 * 0 = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h, Fin.succ_inj]

@[simp] theorem arrow_vertex_source (i : Fin l) :
    arrow k l i * vertex k l i.castSucc = arrow k l i := by
  apply Prod.ext <;> funext j
  · change (0:k) * (Pi.single i.castSucc 1 : Fin (l+1) → k) j = 0
    simp
  · change 0 * 0 + (Pi.single i 1 : _ → k) j * (Pi.single i.castSucc 1 : _ → k) j.castSucc = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h, Fin.castSucc_inj]

/-- The terminal simple right module is the character at vertex l. -/
def terminalCharacter : ChainAlgebra k l →ₐ[k] k where
  toFun x := x.1 (Fin.last l)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
end ChainAlgebra

variable (B : Type u) [Ring B] [Algebra k B]
/-- The actual ordinary algebra D of Section 5. -/
abbrev AlgebraD := B × (B ⊗[k] ChainAlgebra k l)
instance finiteDimensionalD [FiniteDimensional k B] :
    FiniteDimensional k (AlgebraD k l B) := inferInstance
end LittleFinitistic.OrdinarySimulation

end

end OAI
