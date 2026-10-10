import Mathlib
import OAI.Analysis.Commutator.CoefficientForm
import OAI.Analysis.Commutator.CoefficientForm2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

open UniformSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def completionIsometry (U : E →ₗᵢ[ℂ] F) : Completion E →ₗᵢ[ℂ] Completion F where
  toLinearMap := U.toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma completionIsometry_coe (U : E →ₗᵢ[ℂ] F) (x : E) :
    completionIsometry U (x : Completion E) = (U x : Completion F) := by
  change U.toContinuousLinearMap.completion (x : Completion E) = _
  simp

namespace PreHilbert

variable (E F : PreHilbert)

def powerMap (U : E →ₗᵢ[ℂ] E) : ∀ n, power E n →ₗᵢ[ℂ] power E n
  | 0 => LinearIsometry.id
  | n+1 => TensorProduct.mapIsometry U (powerMap U n)

@[simp] lemma powerMap_pure (U : E →ₗᵢ[ℂ] E) (n : ℕ) (x : Fin n → E) :
    powerMap E U n (pure E n x) = pure E n (fun i => U (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerMap, pure_succ, TensorProduct.mapIsometry_apply,
      TensorProduct.map_tmul, LinearIsometry.coe_toLinearMap, ih]
    rfl

def wordMap (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (n : ℕ) :
    wordSpace E F n →ₗᵢ[ℂ] wordSpace E F n :=
  completionIsometry (TensorProduct.mapIsometry U (powerMap F V n))

@[simp] lemma wordMap_word (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (n : ℕ)
    (d : E) (x : Fin n → F) :
    wordMap E F U V n (word E F n d x) = word E F n (U d) (fun i => V (x i)) := by
  simp only [wordMap, word, completionIsometry_coe, TensorProduct.mapIsometry_apply,
    TensorProduct.map_tmul, LinearIsometry.coe_toLinearMap, powerMap_pure]

end PreHilbert

open PreHilbert

variable (E F : PreHilbert) (k l : ℕ)

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [StarAddMonoid M]

lemma coefficient_invariant
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F)
    (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (C : M → M)
    (hstar : ∀ a, star (C a) = C (star a))
    (hv₀ : ∀ a, v₀ (C a) = U (v₀ a)) (hv₁ : ∀ a, v₁ (C a) = V (v₁ a))
    (hΩ : U Ω = Ω)
    (hY : Y.comp (wordMap E F U V k).toContinuousLinearMap =
      (wordMap E F U V l).toContinuousLinearMap.comp Y)
    (A : Option (Fin k ⊕ Fin l) → M) :
    coefficient E F k l Y Ω v₀ v₁ (fun i => C (A i)) =
      coefficient E F k l Y Ω v₀ v₁ A := by
  have hy (x : wordSpace E F k) :
      Y (wordMap E F U V k x) = wordMap E F U V l (Y x) :=
    congrArg (fun T : wordSpace E F k →L[ℂ] wordSpace E F l => T x) hY
  simp only [coefficient, hstar, hv₀, hv₁]
  rw [← wordMap_word]
  have hx : word E F k Ω (fun i => V (v₁ (A (some (.inl i))))) =
      wordMap E F U V k (word E F k Ω (fun i => v₁ (A (some (.inl i))))) := by
    rw [wordMap_word, hΩ]
  rw [hx, hy, LinearIsometry.inner_map_map]

end Kadison
end

end OAI
