import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitudeRestore
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSupport

namespace OAI

/-! # The unchanged restored prior and the masked one-branch energy -/

namespace Ostmann
open scoped Classical BigOperators

/-- Real-valued finite Fubini in exactly the restored template coordinates. -/
theorem movingReverseTemplate_average_real {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℝ) :
    (∑ x, (∏ i, ν i (x i)) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A,
        (∏ i, ν (movingReverseTemplate n r m (.inl i)) (u i)) *
        ∑ y : MovingRegularSlot n r m → A,
          (∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i)) *
          F (movingRestoreSample n r m u y) := by
  have h := movingReverseTemplate_average n r m ν (fun x => (F x : ℂ))
  exact_mod_cast h

/-- Restoring slots changes neither the compensation law nor the surviving law. -/
theorem movingTemplateRestoredPrior_average_real {A : Type} [Fintype A] (n r m : ℕ)
    (μ : A → ℝ) (ν : MovingRegularSlot n r m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℝ) :
    (∑ x, (∏ i, movingTemplateRestoredPrior n r m μ ν i (x i)) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A, (∏ i, μ (u i)) *
        ∑ y : MovingRegularSlot n r m → A, (∏ i, ν i (y i)) *
          F (movingRestoreSample n r m u y) := by
  simpa only [movingTemplateRestoredPrior, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr] using
    movingReverseTemplate_average_real n r m (movingTemplateRestoredPrior n r m μ ν) F

/-- The actual coefficient supplies the distinctness needed to replace its
masked arithmetic multiplier by the surviving prime-product transform. -/
theorem movingTemplateCoefficient_restored_multiplier {A : Type} [Fintype A]
    (value : A → ℕ) (hprime : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState A → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (u : TreeLeafIndex n × Fin 4 → A)
    (y : MovingRegularSlot n r m → A) (XL XR : ℕ) (g : ∀ q : ℕ, ZMod q → ℂ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun i => ⟨hprime (x i)⟩
    let C := movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s x XL XR
    ‖C‖ ^ 2 * naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s
      (fun i => ((outside.prod * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR =
      ‖C * primeProductTransform g (outside.prod * XL * XR * ∏ i, value (u i))
        (∏ i, value (y i)) s‖ ^ 2 := by
  intro x inst C
  by_cases hC : C = 0
  · simp only [hC, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hi := movingTemplateCoefficient_nonzero_injective value outside μ childBound
    pivotBound V F φ G n (4 + r) m s x XL XR (fun i => hprime (x i)) hC
  have hx (i : MovingRegularSlot n r m) :
      x (movingReverseTemplate n r m (.inr i)) = y i := by
    simp only [x, movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply,
      Sum.elim_inr]
  have hy : Function.Injective (value ∘ y) := by
    intro i j hij
    apply Sum.inr.inj
    apply (movingReverseTemplate n r m).injective
    apply hi
    simpa only [Function.comp_apply, hx] using hij
  have he := naturalRegularMultiplier_restored_primeProduct value hprime n r m u y hy
    g outside.prod XL XR s
  change naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s _ _ XL XR = _ at he
  rw [he, norm_mul, mul_pow]

end Ostmann

end OAI
