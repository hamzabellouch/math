import OAI.Algebra.AuslanderReiten.Algebras.BaseAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Abel

namespace OAI

namespace ArExplicit

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

@[ext]
structure TrivialExtension where
  base : A
  dual : Module.Dual k A

namespace TrivialExtension

variable {k A}

def coordinates : TrivialExtension k A ≃ A × Module.Dual k A where
  toFun a := (a.base, a.dual)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TrivialExtension k A) := coordinates.addCommGroup
instance : Module k (TrivialExtension k A) := coordinates.addEquiv.module k

@[simp] theorem base_zero : (0 : TrivialExtension k A).base = 0 := rfl
@[simp] theorem dual_zero : (0 : TrivialExtension k A).dual = 0 := rfl
@[simp] theorem base_add (a b : TrivialExtension k A) : (a + b).base = a.base + b.base := rfl
@[simp] theorem dual_add (a b : TrivialExtension k A) : (a + b).dual = a.dual + b.dual := rfl
@[simp] theorem base_smul (r : k) (a : TrivialExtension k A) : (r • a).base = r • a.base := rfl
@[simp] theorem dual_smul (r : k) (a : TrivialExtension k A) : (r • a).dual = r • a.dual := rfl

def leftDual (a : A) (φ : Module.Dual k A) : Module.Dual k A where
  toFun c := φ (c * a)
  map_add' c d := by simp [add_mul]
  map_smul' r c := by simp

def rightDual (a : A) (φ : Module.Dual k A) : Module.Dual k A where
  toFun c := φ (a * c)
  map_add' c d := by simp [mul_add]
  map_smul' r c := by simp

@[simp] theorem leftDual_apply (a : A) (φ : Module.Dual k A) (c : A) :
    leftDual a φ c = φ (c * a) := rfl
@[simp] theorem rightDual_apply (a : A) (φ : Module.Dual k A) (c : A) :
    rightDual a φ c = φ (a * c) := rfl

def product (a b : TrivialExtension k A) : TrivialExtension k A :=
  ⟨a.base * b.base, leftDual a.base b.dual + rightDual b.base a.dual⟩

instance : Mul (TrivialExtension k A) := ⟨product⟩
instance : One (TrivialExtension k A) := ⟨⟨1, 0⟩⟩

@[simp] theorem base_one : (1 : TrivialExtension k A).base = 1 := rfl
@[simp] theorem dual_one : (1 : TrivialExtension k A).dual = 0 := rfl
@[simp] theorem base_mul (a b : TrivialExtension k A) : (a * b).base = a.base * b.base := rfl
@[simp] theorem dual_mul_apply (a b : TrivialExtension k A) (c : A) :
    (a * b).dual c = b.dual (c * a.base) + a.dual (b.base * c) := rfl

instance : Ring (TrivialExtension k A) where
  __ := (inferInstance : AddCommGroup (TrivialExtension k A))
  mul_assoc a b c := by
    apply TrivialExtension.ext
    · simp only [base_mul, mul_assoc]
    · ext d
      simp [mul_assoc, add_assoc]
  one_mul a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  mul_one a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  left_distrib a b c := by
    apply TrivialExtension.ext
    · simp [mul_add]
    · ext d; simp [add_mul]; abel
  right_distrib a b c := by
    apply TrivialExtension.ext
    · simp [add_mul]
    · ext d; simp [mul_add]; abel
  zero_mul a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  mul_zero a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp

instance : Algebra k (TrivialExtension k A) :=
  Algebra.ofModule
    (by
      intro r a b
      apply TrivialExtension.ext
      · simp
      · ext d; simp [mul_add])
    (by
      intro r a b
      apply TrivialExtension.ext
      · simp
      · ext d; simp [mul_add])

def inl (a : A) : TrivialExtension k A := ⟨a, 0⟩

def inr (φ : Module.Dual k A) : TrivialExtension k A := ⟨0, φ⟩

def inlHom : A →ₐ[k] TrivialExtension k A where
  toFun := inl
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]
  map_mul' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]

theorem inlHom_injective : Function.Injective (inlHom : A →ₐ[k] TrivialExtension k A) := by
  intro a b h
  exact congrArg TrivialExtension.base h

@[simp] theorem inr_mul_inr (φ ψ : Module.Dual k A) :
    inr φ * inr ψ = (0 : TrivialExtension k A) := by
  apply TrivialExtension.ext
  · simp [inr]
  · ext d; simp [inr]

def trace : TrivialExtension k A →ₗ[k] k where
  toFun a := a.dual 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem trace_apply (a : TrivialExtension k A) : trace a = a.dual 1 := rfl

theorem trace_mul (a b : TrivialExtension k A) :
    trace (a * b) = b.dual a.base + a.dual b.base := by simp

theorem trace_mul_comm (a b : TrivialExtension k A) : trace (a * b) = trace (b * a) := by
  simp only [trace_mul, add_comm]

def traceForm : LinearMap.BilinForm k (TrivialExtension k A) where
  toFun a :=
    { toFun := fun b => trace (a * b)
      map_add' b c := by simp [mul_add]
      map_smul' r b := by simp }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' r a := by ext b; simp

@[simp] theorem traceForm_apply (a b : TrivialExtension k A) :
    traceForm a b = trace (a * b) := rfl

theorem traceForm_symmetric : (traceForm : LinearMap.BilinForm k (TrivialExtension k A)).IsSymm :=
  ⟨trace_mul_comm⟩

theorem traceForm_associative (a b c : TrivialExtension k A) :
    traceForm (a * b) c = traceForm a (b * c) := by simp only [traceForm_apply, mul_assoc]

def coordinateLinearEquiv : TrivialExtension k A ≃ₗ[k] A × Module.Dual k A where
  __ := coordinates
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Field

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

theorem traceForm_nondegenerate :
    (traceForm : LinearMap.BilinForm k (TrivialExtension k A)).Nondegenerate := by
  have left : ∀ a : TrivialExtension k A, (∀ b, traceForm a b = 0) → a = 0 := by
    intro a ha
    have hb : a.base = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff k a.base).mp
      intro φ
      simpa [trace_mul, inr] using ha (inr φ)
    have hd : a.dual = 0 := by
      ext b
      simpa [trace_mul, inl] using ha (inl b)
    exact TrivialExtension.ext hb hd
  constructor
  · exact left
  · intro a ha
    apply left a
    intro b
    rw [traceForm_apply, trace_mul_comm]
    exact ha b

instance [Module.Finite k A] : Module.Finite k (TrivialExtension k A) :=
  Module.Finite.equiv coordinateLinearEquiv.symm

theorem finrank_eq_twice [Module.Finite k A] :
    Module.finrank k (TrivialExtension k A) = 2 * Module.finrank k A := by
  rw [coordinateLinearEquiv.finrank_eq, Module.finrank_prod, Subspace.dual_finrank_eq]
  simp [two_mul]

end Field
end TrivialExtension

abbrev T (k : Type*) [Field k] (q : k) := TrivialExtension k (BaseAlgebra k q)

theorem T_finrank (k : Type*) [Field k] (q : k) : Module.finrank k (T k q) = 20 := by
  rw [TrivialExtension.finrank_eq_twice, BaseAlgebra.finrank_eq_ten]

namespace T

variable {k : Type*} [Field k] (q : k)

def coordinateFunctional (i : Letter) : Module.Dual k (BaseAlgebra k q) where
  toFun a := a.coeff i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lower (i : Letter) : T k q := TrivialExtension.inl (BaseAlgebra.basisVector q i)

def upper (i : Letter) : T k q := TrivialExtension.inr (coordinateFunctional q i)

theorem trace_lower_upper (i l : Letter) :
    TrivialExtension.trace (lower q i * upper q l) = if i = l then 1 else 0 := by
  rw [TrivialExtension.trace_mul]
  change (BaseAlgebra.basisVector q i).coeff l + 0 = _
  simp only [BaseAlgebra.coeff_basisVector, add_zero, eq_comm]

theorem trace_upper_lower (i l : Letter) :
    TrivialExtension.trace (upper q i * lower q l) = if i = l then 1 else 0 := by
  rw [TrivialExtension.trace_mul_comm, trace_lower_upper]
  simp only [eq_comm]

theorem upper_mul_upper (i l : Letter) : upper q i * upper q l = 0 :=
  TrivialExtension.inr_mul_inr _ _

end T

end ArExplicit

end OAI
