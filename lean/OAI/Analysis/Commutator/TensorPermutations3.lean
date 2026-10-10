import Mathlib
import OAI.Analysis.Commutator.HilbertTensors2
import OAI.Analysis.Commutator.TensorPermutations2

namespace OAI

noncomputable section

noncomputable section

open scoped TensorProduct

namespace Kadison

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

namespace PreHilbert

end PreHilbert

end Kadison

namespace Kadison.PreHilbert

end Kadison.PreHilbert

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Kadison

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

namespace Kadison

section Gram

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Gram

end Kadison

namespace Kadison

section GramEquiv

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end GramEquiv

namespace PreHilbert

def permute (E : PreHilbert) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    power E n ≃ₗᵢ[ℂ] power E n :=
  gramEquiv (pure E n) (fun v => pure E n (v ∘ σ)) (span_pure E n)
    (by
      have hr : Set.range (fun v => pure E n (v ∘ σ)) = Set.range (pure E n) := by
        ext x
        constructor
        · rintro ⟨v, rfl⟩; exact ⟨v ∘ σ, rfl⟩
        · rintro ⟨v, rfl⟩
          refine ⟨v ∘ σ.symm, ?_⟩
          exact congrArg (pure E n) (funext fun i => by simp)
      rw [hr, span_pure])
    (by
      intro v w
      simp only [inner_pure, Function.comp_apply]
      exact Equiv.prod_comp σ (fun i => inner ℂ (v i) (w i)))

@[simp] theorem permute_pure (E : PreHilbert) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → E) : permute E n σ (pure E n v) = pure E n (v ∘ σ) :=
  gramEquiv_apply _ _ _ _ _ _

def hilbertPermute (E : PreHilbert) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    hilbertPower E n ≃ₗᵢ[ℂ] hilbertPower E n :=
  (permute E n σ).toLinearEquiv.extendOfIsometry
    (UniformSpace.Completion.toComplₗᵢ.toLinearMap)
    (UniformSpace.Completion.toComplₗᵢ.toLinearMap)
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (by intro x; simp)

@[simp] theorem hilbertPermute_pure (E : PreHilbert) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    hilbertPermute E n σ (hilbertPure E n v) = hilbertPure E n (v ∘ σ) := by
  change ((permute E n σ).toLinearEquiv.extendOfIsometry _ _ _ _ _)
      ((UniformSpace.Completion.toComplₗᵢ : power E n →ₗᵢ[ℂ] hilbertPower E n).toLinearMap (pure E n v)) = _
  erw [LinearEquiv.extendOfIsometry_eq]
  change (permute E n σ (pure E n v) : UniformSpace.Completion (power E n)) = _
  rw [permute_pure]
  rfl

theorem eq_zero_of_hilbertPure_inner (E : PreHilbert) (n : ℕ)
    (x : hilbertPower E n) (h : ∀ v, inner ℂ (hilbertPure E n v) x = 0) : x = 0 := by
  apply UniformSpace.Completion.denseRange_coe.eq_zero_of_inner_right ℂ
  intro y
  have hy : y ∈ Submodule.span ℂ (Set.range (pure E n)) := by rw [span_pure]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact h v
  | zero => rw [UniformSpace.Completion.coe_zero, inner_zero_left]
  | add a b _ _ ha hb => rw [UniformSpace.Completion.coe_add, inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [UniformSpace.Completion.coe_smul, inner_smul_left, ha, mul_zero]

theorem continuousLinearMap_ext_pure (E : PreHilbert) (n : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S T : hilbertPower E n →L[ℂ] F)
    (h : ∀ v, S (hilbertPure E n v) = T (hilbertPure E n v)) : S = T := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq S.continuous T.continuous) ?_
  intro y
  have hy : y ∈ Submodule.span ℂ (Set.range (pure E n)) := by rw [span_pure]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact h v
  | zero => rw [UniformSpace.Completion.coe_zero, map_zero, map_zero]
  | add a b _ _ ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]
  | smul c a _ ha => simp only [UniformSpace.Completion.coe_smul, map_smul, ha]

end PreHilbert

end Kadison
end
end

end OAI
