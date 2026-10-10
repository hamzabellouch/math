import OAI.Algebra.Finitistic.Bar.TwoSided
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The balancing relations for the right A-action d·a = d*f(a). -/
def relations : Submodule D (D ⊗[k] V) :=
  Submodule.span D {z | ∃ (d : D) (a : A) (v : V),
    z = (d * f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)}

/-- Noncommutative balanced tensor D ⊗_A V, presented using tensors over the field. -/
abbrev tensor := (D ⊗[k] V) ⧸ relations f V

/-- Its canonical D-linear quotient map. -/
def quotient : D ⊗[k] V →ₗ[D] tensor f V := (relations f V).mkQ

omit [IsScalarTower k A V] in
/-- The defining balanced relation, as an equality in the actual quotient module. -/
theorem balanced (d : D) (a : A) (v : V) :
    quotient f V ((d*f a) ⊗ₜ[k] v) = quotient f V (d ⊗ₜ[k] (a • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨d, a, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Balanced tensor acts on all A-linear maps. -/
theorem map_relations (h : V →ₗ[A] W) : relations f V ≤
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change quotient f W ((AlgebraTensorModule.lTensor D D (h.restrictScalars k))
    ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[A] W) : tensor f V →ₗ[D] tensor f W :=
  (relations f V).liftQ
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k)))
    (map_relations f V W h)

@[simp] theorem map_quotient_tmul (h : V →ₗ[A] W) (d : D) (v : V) :
    map f V W h (quotient f V (d ⊗ₜ[k] v)) = quotient f W (d ⊗ₜ[k] h v) := rfl

/-- Composition preservation for the actual balanced tensor, proved from its quotient presentation. -/
theorem map_comp (h : V →ₗ[A] W) (g : W →ₗ[A] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  change quotient f W (d ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl
end Maps

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Evaluation of D ⊗_k (A ⊗_k W) on the two leading coefficients. -/
def collapse : D ⊗[k] (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (DerivedBar.action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (FreeBaseChange.coefficient f W))

@[simp] theorem collapse_tmul (d : D) (z : A ⊗[k] W) :
    collapse f W (d ⊗ₜ[k] z) = d • FreeBaseChange.coefficient f W z := rfl

/-- The evaluation kills all balancing relations, without commutativity of A or D. -/
theorem relations_le_ker_collapse : relations f (A ⊗[k] W) ≤ (collapse f W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change collapse f W ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)) = 0
  rw [map_sub, collapse_tmul, collapse_tmul, FreeBaseChange.coefficient_smul,
    mul_smul, sub_self]

/-- Descent of coefficient evaluation to the balanced tensor. -/
def descend : tensor f (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (relations f (A ⊗[k] W)).liftQ (collapse f W) (relations_le_ker_collapse f W)

/-- The inverse inserts a unit A coefficient before taking the balanced quotient. -/
def insert : D ⊗[k] W →ₗ[D] tensor f (A ⊗[k] W) :=
  (quotient f (A ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (TensorProduct.mk k A W 1))

@[simp] theorem descend_quotient (z : D ⊗[k] (A ⊗[k] W)) :
    descend f W (quotient f (A ⊗[k] W) z) = collapse f W z := rfl

@[simp] theorem insert_tmul (d : D) (w : W) :
    insert f W (d ⊗ₜ[k] w) = quotient f (A ⊗[k] W) (d ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

/-- One inverse identity of the actual balanced free-module tensor equivalence. -/
theorem descend_insert : (descend f W).comp (insert f W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d w
  simp [LinearMap.comp_apply, TensorProduct.smul_tmul']

/-- The other inverse identity follows from balancing, not from flatness. -/
theorem insert_descend : (insert f W).comp (descend f W) = LinearMap.id := by
  apply (relations f (A ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp_all [TensorProduct.tmul_add]
  | tmul a w =>
    change insert f W (collapse f W (d ⊗ₜ[k] (a ⊗ₜ[k] w))) =
      quotient f (A ⊗[k] W) (d ⊗ₜ[k] (a ⊗ₜ[k] w))
    rw [collapse_tmul, FreeBaseChange.coefficient_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']

/-- The standard identification D ⊗_A (A ⊗_k W) ≅ D ⊗_k W for arbitrary algebras. -/
def freeEquiv : tensor f (A ⊗[k] W) ≃ₗ[D] D ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend f W) (insert f W) (descend_insert f W) (insert_descend f W)

end DerivedBar.Balanced

end

end OAI
