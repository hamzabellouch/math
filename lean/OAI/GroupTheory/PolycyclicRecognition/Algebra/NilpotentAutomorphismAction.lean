import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentModelIntegration

namespace OAI

/-! # Integrating a continuous action on a nilpotent Lie algebra

The group laws follow by checking the global exponential coordinates. Those
same coordinates give joint continuity, rather than merely continuity of each
automorphism separately.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L K : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group K] [TopologicalSpace K]

theorem exists_nilpotent_automorphism_action
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp)
    (ρ : K →* (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ[ℝ]
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier))
    (hρlie : ∀ k x y, ρ k ⁅x, y⁆ = ⁅ρ k x, ρ k y⁆)
    (hρcont : Continuous (fun p : K × GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ρ p.1 p.2)) :
    ∃ α : K →* MulAut N.carrier,
      Continuous (fun p : K × N.carrier => α p.1 p.2) ∧
      (∀ k x, α k (Exp x) = Exp (ρ k x)) ∧
      ∀ k, ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ (α k) := by
  obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar L N).2 Exp hExp
    (N.tangent_nilpotent hnil)).1
  have hex (k : K) : ∃ f : N.carrier →* N.carrier,
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ f ∧
      ∀ x, f (Exp x) = Exp (ρ k x) := by
    let j : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier →ₗ⁅ℝ⁆
        GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier :=
      { __ := (ρ k).toLinearMap
        map_lie' := fun {x y} => hρlie k x y }
    obtain ⟨f, hf, _, he⟩ := nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput L N) inferInstance (N.tangent_nilpotent hnil)
      j Exp Exp hExp hExp
    exact ⟨f, hf, he⟩
  choose F hFsmooth hFexp using hex
  have hFone (x : N.carrier) : F 1 x = x := by
    obtain ⟨v, hv⟩ := c.surjective x
    rw [hc] at hv
    rw [← hv, hFexp, map_one]
    rfl
  have hFmul (k l : K) (x : N.carrier) : F (k * l) x = F k (F l x) := by
    obtain ⟨v, hv⟩ := c.surjective x
    rw [hc] at hv
    rw [← hv, hFexp, hFexp, hFexp, map_mul]
    rfl
  let a (k : K) : MulAut N.carrier :=
    { toFun := F k
      invFun := F k⁻¹
      left_inv := fun x => by rw [← hFmul, inv_mul_cancel, hFone]
      right_inv := fun x => by rw [← hFmul, mul_inv_cancel, hFone]
      map_mul' := (F k).map_mul }
  let α : K →* MulAut N.carrier :=
    { toFun := a
      map_one' := by ext x; exact hFone x
      map_mul' := by intro k l; ext x; exact hFmul k l x }
  refine ⟨α, ?_, hFexp, hFsmooth⟩
  change Continuous (fun p : K × N.carrier => F p.1 p.2)
  have he : (fun p : K × N.carrier => F p.1 p.2) =
      (fun p => c (ρ p.1 (c.symm p.2))) := by
    funext p
    have h := hFexp p.1 (c.symm p.2)
    rw [← hc, c.apply_symm_apply, ← hc] at h
    exact h
  rw [he]
  exact c.continuous.comp (hρcont.comp
    (continuous_fst.prodMk (c.symm.continuous.comp continuous_snd)))

end PolycyclicRecognition

end

end OAI
