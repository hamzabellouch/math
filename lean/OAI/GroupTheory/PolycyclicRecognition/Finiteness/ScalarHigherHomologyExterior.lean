import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingBarEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExtendedH2CrossProduct

namespace OAI

/-! # Higher rational homology maps onto exterior powers

The map is built on the actual bar complex. Signed permutation cycles give
preimages of pure wedges after division by the factorial of the degree.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K A : Type) [Field K] [CommGroup A]

def scalarIntegralExterior (n : ℕ) :
    Additive A [⋀^Fin n]→ₗ[ℤ] (⋀[K]^n (K ⊗[ℤ] Additive A)) where
  toMultilinearMap :=
    ((exteriorPower.ιMulti K n).toMultilinearMap.restrictScalars ℤ).compLinearMap
      (fun _ => scalarTensorUnit K (Additive A))
  map_eq_zero_of_eq' _ _ _ h hij :=
    (exteriorPower.ιMulti K n).map_eq_zero_of_eq _
      (congrArg (scalarTensorUnit K (Additive A)) h) hij

@[simp] theorem scalarIntegralExterior_apply (n : ℕ) (v : Fin n → Additive A) :
    scalarIntegralExterior K A n v =
      exteriorPower.ιMulti K n (fun i => scalarTensorUnit K (Additive A) (v i)) := rfl

def scalarHomologyExterior (n : ℕ) :
    (K ⊗[ℤ] groupHomology (integralTrivialCoefficient A) n) →ₗ[K]
      (⋀[K]^n (K ⊗[ℤ] Additive A)) :=
  scalarExtensionLinear K
    (abelianMultilinearHomology (scalarIntegralExterior K A n).toMultilinearMap)

theorem scalarHomologyExterior_class {n : ℕ} (r : K) (v : Fin (n + 1) → A) :
    scalarHomologyExterior K A (n + 1) (r ⊗ₜ[ℤ] alternatingBarClass v) =
      r • (((n + 1).factorial : ℤ) •
        exteriorPower.ιMulti K (n + 1)
          (fun i => scalarTensorUnit K (Additive A) (Additive.ofMul (v i)))) := by
  rw [scalarHomologyExterior, scalarExtensionLinear_tmul,
    abelianMultilinearHomology_alternating]
  rfl

theorem scalarTensorUnit_span (M : Type) [AddCommGroup M] [Module ℤ M] :
    Submodule.span K (Set.range (scalarTensorUnit K M)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    have h := (Submodule.span K (Set.range (scalarTensorUnit K M))).smul_mem r
      (Submodule.subset_span (Set.mem_range_self a))
    change r • ((1 : K) ⊗ₜ[ℤ] a) ∈ _ at h
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem scalarHomologyExterior_surjective_of_factorial_ne_zero (n : ℕ)
    (hn : ((n + 1).factorial : K) ≠ 0) :
    Function.Surjective (scalarHomologyExterior K A (n + 1)) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span K (n + 1) (K ⊗[ℤ] Additive A)
    (scalarTensorUnit_span K (Additive A))]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  choose a ha using fun i => hv (Set.mem_range_self i)
  refine ⟨((n + 1).factorial : K)⁻¹ ⊗ₜ[ℤ]
    alternatingBarClass (fun i => (a i).toMul), ?_⟩
  rw [scalarHomologyExterior_class]
  have he : (fun i => scalarTensorUnit K (Additive A) (Additive.ofMul (a i).toMul)) = v := by
    funext i
    exact ha i
  rw [he]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem scalarHomologyExterior_surjective [CharZero K] (n : ℕ) :
    Function.Surjective (scalarHomologyExterior K A (n + 1)) :=
  scalarHomologyExterior_surjective_of_factorial_ne_zero K A n
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end PolycyclicRecognition

end

end OAI
