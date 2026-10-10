import OAI.NumberTheory.Ostmann.Arithmetic.MovingSymmetrizedProductLower
import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedTemplateEnergy

namespace OAI

/-! # The restored multiplier of the actual bulk-averaged coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingBulkAveragedTemplateCoefficient {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (x : MovingRegularSlot n r m → A) (XL XR : ℕ) : ℂ :=
  mixedBulkSymmetrize n m (movingTemplateBulk n r m)
    (fun _ y _ _ => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y XL XR) 0 x 0 0

theorem movingBulkAveragedTemplateCoefficient_restore {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) (XL XR : ℕ) :
    movingBulkAveragedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u y) XL XR =
    movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s u y XL XR := by
  simp only [movingBulkAveragedTemplateCoefficient, movingSymmetrizedTemplateCoefficient,
    mixedBulkSymmetrize, finiteFamilyAverage, movingRestoreSample_bulk_action]

theorem movingBulkAveragedTemplateCoefficient_nonzero_injective {A : Type} [Fintype A]
    (value : A → ℕ) (hprime : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (x : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (h : movingBulkAveragedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s x XL XR ≠ 0) : Function.Injective (value ∘ x) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m) _ 0 x 0 0 h
  have hi := movingTemplateCoefficient_nonzero_injective value outside μ childBound pivotBound V
    F φ G n r m s (selectedBulkSample (movingTemplateBulk n r m) e x) XL XR
    (fun i => hprime _) he
  exact (selectedBulkSample_injective_iff (movingTemplateBulk n r m) e value x).mp hi

noncomputable def movingSymmetrizedMaskedTemplateKernel
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) : ℝ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  ‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n (4 + r) m s x p X‖ ^ 2 *
    naturalRegularMultiplier q (movingRestoredActive n r m) s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) p X

theorem movingSymmetrizedMaskedTemplateKernel_restore
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n r m → P)
    (p X : ℕ) (s : ℤ) :
    movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg
      (movingRestoreSample n r m u y) p X s =
    ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m s u y p X *
      primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * X)
        (∏ i, (y i : ℕ)) s‖ ^ 2 := by
  unfold movingSymmetrizedMaskedTemplateKernel
  dsimp only
  rw [movingBulkAveragedTemplateCoefficient_restore]
  by_cases hC : movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      F φ G n r m s u y p X = 0
  · simp only [hC, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hfull : Function.Injective (Subtype.val ∘ movingRestoreSample n r m u y) :=
    movingBulkAveragedTemplateCoefficient_nonzero_injective Subtype.val
      (fun a => hP _ a.property) outside μ childBound pivotBound V F φ G n (4 + r) m s
      (movingRestoreSample n r m u y) p X (by rwa [movingBulkAveragedTemplateCoefficient_restore])
  have hy : Function.Injective (Subtype.val ∘ y) := by
    intro i j hij
    apply Sum.inr.inj
    apply (movingReverseTemplate n r m).injective
    apply hfull
    simpa only [Function.comp_apply, movingRestoreSample, Equiv.symm_apply_apply,
      Sum.elim_inr] using hij
  have he := naturalRegularMultiplier_restored_primeProduct Subtype.val
    (fun a : P => hP _ a.property) n r m u y hy greg outside.prod p X s
  dsimp only at he
  simp only [Function.comp_def] at he
  rw [he, norm_mul, mul_pow]
  congr 3
  ac_rfl

end Ostmann

end OAI
