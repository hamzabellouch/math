import OAI.Algebra.AuslanderReiten.Algebras.FrobeniusTrace
import OAI.Algebra.AuslanderReiten.Algebras.TensorStructure
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

namespace ArExplicit.FrobeniusTrace

open TensorProduct

variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [Module.Finite k R] [Module.Finite k S]
variable (τ : FrobeniusTrace k R) (σ : FrobeniusTrace k S)

noncomputable def tensorTrace : R ⊗[k] S →ₗ[k] k :=
  TensorProduct.dualDistrib k R S (τ.trace ⊗ₜ[k] σ.trace)

omit [Module.Finite k R] [Module.Finite k S] in
@[simp] theorem tensorTrace_tmul (r : R) (s : S) :
    tensorTrace τ σ (r ⊗ₜ[k] s) = τ.trace r * σ.trace s := rfl

noncomputable def tensorDualEquiv : R ⊗[k] S ≃ₗ[k] Module.Dual k (R ⊗[k] S) :=
  (TensorProduct.congr τ.dualEquiv σ.dualEquiv).trans
    (TensorProduct.dualDistribEquiv k R S)

theorem tensorDualEquiv_apply (a b : R ⊗[k] S) :
    tensorDualEquiv τ σ a b = tensorTrace τ σ (b * a) := by
  induction a with
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, mul_add, ha, ha']
  | tmul r s =>
      induction b with
      | add b b' hb hb' => simp only [map_add, add_mul, hb, hb']
      | tmul r' s' =>
          simp [tensorDualEquiv, tensorTrace, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

noncomputable def tensor : FrobeniusTrace k (R ⊗[k] S) where
  trace := tensorTrace τ σ
  separates a ha := by
    apply (tensorDualEquiv τ σ).injective
    rw [map_zero]
    apply LinearMap.ext
    intro b
    exact (tensorDualEquiv_apply τ σ a b).trans (ha b)

omit [Module.Finite k R] [Module.Finite k S] in
theorem tensorTrace_mul_comm
    (hτ : ∀ a b, τ.trace (a * b) = τ.trace (b * a))
    (hσ : ∀ a b, σ.trace (a * b) = σ.trace (b * a)) (a b : R ⊗[k] S) :
    tensorTrace τ σ (a * b) = tensorTrace τ σ (b * a) := by
  induction a with
  | add a a' ha ha' => simp only [add_mul, mul_add, map_add, ha, ha']
  | tmul r s =>
      induction b with
      | add b b' hb hb' => simp only [add_mul, mul_add, map_add, hb, hb']
      | tmul r' s' => simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul, hτ, hσ]

end ArExplicit.FrobeniusTrace

namespace ArExplicit

noncomputable def AFrobeniusTrace (k : Type*) [Field k] (q : k) : FrobeniusTrace k (A k q) :=
  (trivialExtensionFrobeniusTrace k (BaseAlgebra k q)).tensor
    (trivialExtensionFrobeniusTrace k (BaseAlgebra k q))

instance (k : Type*) [Field k] (q : k) : Module.Injective (A k q) (A k q) :=
  (AFrobeniusTrace k q).regular_injective

theorem A_trace_symmetric (k : Type*) [Field k] (q : k) (a b : A k q) :
    (AFrobeniusTrace k q).trace (a * b) = (AFrobeniusTrace k q).trace (b * a) :=
  FrobeniusTrace.tensorTrace_mul_comm _ _ TrivialExtension.trace_mul_comm
    TrivialExtension.trace_mul_comm a b

end ArExplicit

end OAI
