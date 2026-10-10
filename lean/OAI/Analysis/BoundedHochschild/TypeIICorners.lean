import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CenterCorners

namespace OAI

/-! Weak powers of partial unitaries in type-II corners. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildSakai HochschildCorners HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]
include e hq in
theorem exists_partial_unitary_weak_powers_of_typeII1
    (hτ : TraceInPredual e τ) (_h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : FinitePathMain.TypeII1 M) (hq0 : q ≠ 0)
    (a : I → M) (k : I → Bool × ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ w : PartialUnitary M, w.support=q ∧ ∀ i, ‖τ (a i*w.power (k i))‖<ε*(τ q).re := by
  let eC := cornerPredualEquiv q hq e
  let ρ := cornerTrace q hq τ
  let b : I → Corner q hq := fun i => ⟨q*a i*q,compress_mem_corner hq (a i)⟩
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  obtain ⟨u,hu⟩ := HochschildMatrixSystems.exists_unitary_weak_powers_of_typeII1 eC ρ
    (cornerTrace_normal q hq e τ hτ) (cornerTrace_one q hq τ hfaith hq0)
    (cornerTrace_tracial q hq τ htr) (cornerTrace_faithful q hq τ hfaith hq0)
    (HochschildCentralQuantization.corner_typeII1 e τ hτ htr hfaith hq hq0 hII) b (fun i => signedExponent (k i)) (fun i => signedExponent_ne_zero _) hε
  refine ⟨ofCornerUnitary q hq u,ofCornerUnitary_support q hq u,fun i => ?_⟩
  let v : Corner q hq := (u^signedExponent (k i) : unitary (Corner q hq))
  have hvq : (v:M)*q=(v:M) := v.property.2
  have hqv : q*(v:M)=(v:M) := v.property.1
  have he : τ ((b i*v : Corner q hq):M)=τ (a i*(v:M)) := by
    change τ (q*a i*q*(v:M))=_
    calc
      _ = τ (q*(a i*(v:M))) := by rw [mul_assoc,mul_assoc,hqv]
      _ = τ ((a i*(v:M))*q) := htr _ _
      _ = _ := by rw [mul_assoc,hvq]
  have hh := hu i
  change ‖cornerTrace q hq τ (b i*v)‖<ε at hh
  rw [cornerTrace_apply,he,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hh
  rw [ofCornerUnitary_power]
  have hh' := (mul_lt_mul_of_pos_left hh ht)
  simpa only [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm (τ q).re ε] using hh'
end HochschildPatching

end

end OAI
