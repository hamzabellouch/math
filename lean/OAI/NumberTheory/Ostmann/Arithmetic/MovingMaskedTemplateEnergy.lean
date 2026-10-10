import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeHarmonicCost

namespace OAI

/-! # The one-branch energy with its actual compensation mask -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRestoredCompensationProduct {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (x : MovingRegularSlot n (4 + r) m → A) : ℕ :=
  ∏ i : TreeLeafIndex n × Fin 4, value (x (movingReverseTemplate n r m (.inl i)))

@[simp] theorem movingRestoredCompensationProduct_restore {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    movingRestoredCompensationProduct value n r m (movingRestoreSample n r m u y) =
      ∏ i, value (u i) := by
  simp only [movingRestoredCompensationProduct, movingRestoreSample,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

noncomputable def movingMaskedTemplateKernel
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) : ℝ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n (4 + r) m s x p X‖ ^ 2 *
    naturalRegularMultiplier q (movingRestoredActive n r m) s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) p X

theorem movingMaskedTemplateKernel_restore
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n r m → P)
    (p X : ℕ) (s : ℤ) :
    movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg
      (movingRestoreSample n r m u y) p X s =
    ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n (4 + r) m s (movingRestoreSample n r m u y) p X *
      primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * X)
        (∏ i, (y i : ℕ)) s‖ ^ 2 := by
  have he := movingTemplateCoefficient_restored_multiplier Subtype.val
    (fun a : P => hP _ a.property) outside μ childBound pivotBound V F φ G n r m s u y p X greg
  dsimp only at he
  unfold movingMaskedTemplateKernel
  dsimp only
  convert he using 1
  congr 3
  ac_rfl

noncomputable def movingMaskedTemplateEnergy
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) : ℝ :=
  ∑ x : MovingRegularSlot n (4 + r) m → P,
    (∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)) *
      (weight x * ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
        ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
          ∑ s : transferFrequencyRange (V n),
            movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m
              greg x p X s.val)

theorem movingMaskedTemplateKernel_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) :
    0 ≤ movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s := by
  unfold movingMaskedTemplateKernel
  dsimp only
  apply mul_nonneg (sq_nonneg _)
  unfold naturalRegularMultiplier
  apply Finset.prod_nonneg
  intro i _
  split <;> positivity

/-- A bound on the original support suffices: no support is conditioned into
or removed from the independent restored law. -/
theorem movingMaskedTemplateEnergy_weight_le
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) (B : ℝ)
    (hweight : ∀ x, (∏ i, movingTemplateRestoredPrior n r m (μ n)
      (fun i => primeSubsetPrior P (Q i)) i (x i)) ≠ 0 → weight x ≤ B) :
    movingMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg weight ≤
      B * movingMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg (fun _ => 1) := by
  unfold movingMaskedTemplateEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  let mass := ∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)
  have hm : 0 ≤ mass := by
    apply Finset.prod_nonneg
    intro i _
    unfold movingTemplateRestoredPrior
    cases he : (movingReverseTemplate n r m).symm i with
    | inl j => exact hμ n (x i)
    | inr j => exact primeSubsetPrior_nonneg P (Q j) (x i)
  by_cases hz : mass = 0
  · change mass * _ ≤ B * (mass * _)
    simp only [hz, zero_mul, mul_zero, le_refl]
  have hE : 0 ≤ ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
        ∑ s : transferFrequencyRange (V n),
          movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s.val := by
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (hφ _)
    apply Finset.sum_nonneg
    intro X _
    apply mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ X)
    exact Finset.sum_nonneg (fun s _ => movingMaskedTemplateKernel_nonneg P hP outside μ
      childBound pivotBound V F φ G n r m greg x p X s.val)
  have ht := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hweight x hz) hE) hm
  convert ht using 1
  ring

/-- The compensation product is bounded using only the support of the same
original prior. All four draws at every leaf are counted. -/
theorem movingRestoredCompensationProduct_le_exp
    (P : Finset ℕ) (μ : P → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (b : ℝ)
    (hb : ∀ a, μ a ≠ 0 → (a : ℝ) ≤ Real.exp b)
    (x : MovingRegularSlot n (4 + r) m → P)
    (hx : (∏ i, movingTemplateRestoredPrior n r m μ ν i (x i)) ≠ 0) :
    (movingRestoredCompensationProduct Subtype.val n r m x : ℝ) ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) := by
  have hm (i : TreeLeafIndex n × Fin 4) :
      μ (x (movingReverseTemplate n r m (.inl i))) ≠ 0 := by
    have h := Finset.prod_ne_zero_iff.mp hx (movingReverseTemplate n r m (.inl i))
      (Finset.mem_univ _)
    simpa only [movingTemplateRestoredPrior, Equiv.symm_apply_apply, Sum.elim_inl] using h
  calc
    (movingRestoredCompensationProduct Subtype.val n r m x : ℝ) =
        ∏ i : TreeLeafIndex n × Fin 4, (x (movingReverseTemplate n r m (.inl i)) : ℝ) := by
      simp only [movingRestoredCompensationProduct, Nat.cast_prod]
    _ ≤ ∏ _i : TreeLeafIndex n × Fin 4, Real.exp b := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact hb _ (hm i)
    _ = Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, card_treeLeafIndex,
        Fintype.card_fin, ← Real.exp_nat_mul]

end Ostmann

end OAI
