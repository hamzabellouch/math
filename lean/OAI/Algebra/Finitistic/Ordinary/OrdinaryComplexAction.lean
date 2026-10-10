import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainAlgebra
import Mathlib.Algebra.BigOperators.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Module

namespace OAI
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k : Type u} [Field k] {l : ℕ}
namespace ChainAlgebra
/-- The coefficient of the unique possible arrow from j to i. -/
def coefficient (x : ChainAlgebra k l) (i j : Fin (l+1)) : k :=
  if h : j.val < l then if i.val = j.val+1 then x.2 ⟨j.val,h⟩ else 0 else 0

@[simp] theorem coefficient_mul (x y : ChainAlgebra k l) (i j : Fin (l+1)) :
    coefficient (x*y) i j = x.1 i * coefficient y i j + coefficient x i j * y.1 j := by
  unfold coefficient
  split
  next h =>
    split
    next hij =>
      have hi : i = (⟨j.val,h⟩ : Fin l).succ := Fin.ext hij
      have hj : j = (⟨j.val,h⟩ : Fin l).castSucc := rfl
      rw [mul_radical, hi]
      rfl
    next h => simp
  next h => simp

@[simp] theorem coefficient_one (i j : Fin (l+1)) :
    coefficient (1 : ChainAlgebra k l) i j = 0 := by
  unfold coefficient
  have hz (j : Fin l) : (1 : ChainAlgebra k l).2 j = 0 := rfl
  split <;> simp [hz]

@[simp] theorem coefficient_zero (i j : Fin (l+1)) :
    coefficient (0 : ChainAlgebra k l) i j = 0 := by
  unfold coefficient
  split <;> simp

@[simp] theorem coefficient_add (x y : ChainAlgebra k l) (i j : Fin (l+1)) :
    coefficient (x+y) i j = coefficient x i j + coefficient y i j := by
  unfold coefficient
  split <;> simp
  split <;> simp

@[simp] theorem coefficient_vertex (h i j : Fin (l+1)) :
    coefficient (vertex k l h) i j = 0 := by
  unfold coefficient
  split <;> simp [vertex]

@[simp] theorem coefficient_arrow (h : Fin l) (i j : Fin (l+1)) :
    coefficient (arrow k l h) i j = if i = h.succ ∧ j = h.castSucc then 1 else 0 := by
  classical
  simp only [coefficient, arrow, Pi.single_apply, Fin.ext_iff,
    Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all

end ChainAlgebra

/-- Actual finite direct sum of terms; the finite product is canonically that sum. -/
abbrev OrdinaryTerms (V : Fin (l+1) → Type v) := ∀ i, V i

namespace OrdinaryTerms
variable (V : Fin (l+1) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (d : ∀ i j, V i →ₗ[k] V j)

/-- Coordinate action induced by the genuine differential, not an assumed representation. -/
def action (x : ChainAlgebra k l) (v : OrdinaryTerms V) (i : Fin (l+1)) : V i :=
  x.1 i • v i + ∑ j, ChainAlgebra.coefficient x i j • d j i (v j)

theorem action_add (x : ChainAlgebra k l) (v w : OrdinaryTerms V) :
    action V d x (v+w) = action V d x v + action V d x w := by
  funext i
  simp only [action, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  abel

theorem action_smul (x : ChainAlgebra k l) (c : k) (v : OrdinaryTerms V) :
    action V d x (c • v) = c • action V d x v := by
  funext i
  simp only [action, Pi.smul_apply, map_smul, smul_add, Finset.smul_sum]
  congr 1
  · exact smul_comm _ _ _
  · apply Finset.sum_congr rfl; intro j _; exact smul_comm _ _ _

/-- The complex equation d²=0 implies associativity of the ordinary action. -/
theorem action_mul (dd : ∀ i j h, (d j h).comp (d i j) = 0)
    (x y : ChainAlgebra k l) (v : OrdinaryTerms V) :
    action V d (x*y) v = action V d x (action V d y v) := by
  have hz (i j h) (w : V i) : d j h (d i j w) = 0 := by
    have := LinearMap.congr_fun (dd i j h) w
    simpa using this
  funext i
  simp only [action, ChainAlgebra.mul_diagonal, ChainAlgebra.coefficient_mul,
    map_add, map_smul, map_sum, hz, smul_zero, Finset.sum_const_zero, add_zero,
    smul_add, Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
  simp only [mul_comm]
  abel

def actionLinear (x : ChainAlgebra k l) : OrdinaryTerms V →ₗ[k] OrdinaryTerms V where
  toFun := action V d x
  map_add' := action_add V d x
  map_smul' := action_smul V d x

/-- Each ordinary vertex projects onto the corresponding genuine term. -/
theorem action_vertex (h : Fin (l+1)) (v : OrdinaryTerms V) :
    action V d (ChainAlgebra.vertex k l h) v = Pi.single h (v h) := by
  classical
  funext i
  simp only [action, ChainAlgebra.coefficient_vertex, zero_smul,
    Finset.sum_const_zero, add_zero]
  change (Pi.single h 1 : Fin (l+1) → k) i • v i = Pi.single h (v h) i
  by_cases hi : i = h
  · subst i; simp
  · simp [hi]

/-- Each ordinary arrow acts by the actual differential on its source term. -/
theorem action_arrow (h : Fin l) (v : OrdinaryTerms V) :
    action V d (ChainAlgebra.arrow k l h) v =
      Pi.single h.succ (d h.castSucc h.succ (v h.castSucc)) := by
  classical
  funext i
  have hz : (ChainAlgebra.arrow k l h).1 i = 0 := rfl
  simp only [action, hz, zero_smul, zero_add, ChainAlgebra.coefficient_arrow]
  by_cases hi : i = h.succ
  · subst i; simp
  · simp [hi]

theorem action_one (v : OrdinaryTerms V) : action V d 1 v = v := by
  funext i
  have ho : (1 : ChainAlgebra k l).1 i = 1 := rfl
  simp [action, ho]

theorem action_zero (v : OrdinaryTerms V) : action V d 0 v = 0 := by
  funext i
  simp only [action, ChainAlgebra.coefficient_zero, zero_smul, Finset.sum_const_zero, add_zero]
  simp [ChainAlgebra.zero_eq]

theorem add_action (x y : ChainAlgebra k l) (v : OrdinaryTerms V) :
    action V d (x+y) v = action V d x v + action V d y v := by
  funext i
  have ha : (x+y).1 i = x.1 i + y.1 i := rfl
  simp only [action, ha, Pi.add_apply, ChainAlgebra.coefficient_add, add_smul, Finset.sum_add_distrib]
  abel

/-- The ordinary C-module constructed from the complex equation. -/
@[instance_reducible]
def module (dd : ∀ i j h, (d j h).comp (d i j) = 0) :
    Module (ChainAlgebra k l) (OrdinaryTerms V) where
  smul := action V d
  one_smul := action_one V d
  mul_smul := action_mul V d dd
  smul_zero x := by
    change action V d x 0 = 0
    funext i
    simp [action]
  smul_add := action_add V d
  add_smul := add_action V d
  zero_smul := action_zero V d

variable (dd : ∀ i j h, (d j h).comp (d i j) = 0)

/-- The constructed action retains the given k-vector-space structure. -/
theorem scalarTower : letI := module V d dd; IsScalarTower k (ChainAlgebra k l) (OrdinaryTerms V) := by
  let := module V d dd
  refine ⟨?_⟩
  intro c x v
  change action V d (c • x) v = c • action V d x v
  funext i
  have hc (i j : Fin (l+1)) :
      ChainAlgebra.coefficient (c • x) i j = c * ChainAlgebra.coefficient x i j := by
    unfold ChainAlgebra.coefficient
    split <;> simp [ChainAlgebra.smul_eq]
  simp only [action, hc]
  simp only [ChainAlgebra.smul_eq, Pi.smul_apply, action,
    smul_eq_mul, mul_smul, smul_add, Finset.smul_sum]
/-- Any additional scalar action commuting with k and with d commutes with C.
Applied to B and Bᵐᵒᵖ this proves both bimodule actions, without postulating them. -/
theorem action_commutes (R : Type*) [Monoid R] [∀ i, DistribMulAction R (V i)]
    [∀ i, SMulCommClass k R (V i)]
    (hd : ∀ i j (r : R) (v : V i), d i j (r • v) = r • d i j v)
    (x : ChainAlgebra k l) (r : R) (v : OrdinaryTerms V) :
    action V d x (r • v) = r • action V d x v := by
  funext i
  simp only [action, Pi.smul_apply, hd, smul_add, Finset.smul_sum]
  congr 1
  · exact smul_comm _ _ _
  · apply Finset.sum_congr rfl; intro j _; exact smul_comm _ _ _

instance finiteDimensional [∀ i, FiniteDimensional k (V i)] :
    FiniteDimensional k (OrdinaryTerms V) := inferInstanceAs (FiniteDimensional k (∀ i, V i))
end OrdinaryTerms
end LittleFinitistic.OrdinarySimulation

end

end OAI
