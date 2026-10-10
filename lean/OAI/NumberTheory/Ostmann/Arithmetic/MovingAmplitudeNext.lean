import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeTerms

namespace OAI

/-! # Identifying the transferred off-diagonal with the next prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateDoubledPrior {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot n r m → σ → ℝ) :
    MovingRegularSlot (n + 1) r m → σ → ℝ :=
  fun i => ν (Sum.elim id id i.1, i.2)

@[simp] theorem movingTemplateDoubledPrior_side {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot n r m → σ → ℝ) (b : Bool)
    (y : MovingRegularSlot n r m → σ) :
    movingTemplateSidePrior n r m (movingTemplateDoubledPrior n r m ν) b y =
      ∏ i, ν i (y i) := by
  cases b <;> rfl

private theorem amplitude_pair_sum {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (ρ : A → ℝ) (ν : B → ℝ) (F : A → A → B → B → C → C → ℂ) :
    (∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
      ∑ x, (ρ x : ℂ) * ∑ z, (ρ z : ℂ) *
        ∑ y, (ν y : ℂ) * ∑ t, (ν t : ℂ) * ∑ v, ∑ w, F x z y t v w := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Complex.ofReal_mul]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext y
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext z
    arg 2
    ext y
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem amplitude_full_sum {U S A B C : Type}
    [Fintype U] [Fintype S] [Fintype A] [Fintype B] [Fintype C]
    (M : U → ℂ) (ρ : A → ℝ) (ν : B → ℝ)
    (F : U → S → A → A → B → B → C → C → ℂ) :
    (∑ u, M u * ∑ s, ∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F u s a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
    ∑ XL, (ρ XL : ℂ) * ∑ XR, (ρ XR : ℂ) * ∑ s, ∑ u, M u *
      ∑ left, (ν left : ℂ) * ∑ right, (ν right : ℂ) * ∑ v, ∑ w,
        F u s XL XR left right v w := by
  simp_rw [amplitude_pair_sum]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XL _
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XR _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The off-diagonal is the next amplitude under the independent doubled
regular law. Both surviving giants retain their common original prior. -/
theorem movingAmplitudeOffDiagonal_eq_next {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingAmplitudeOffDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable := by
  rw [movingTemplatePrimeAmplitude_next value hvalue outside μ childBound pivotBound V hV
    F hF φ G n r m Pg hPg ρ (movingTemplateDoubledPrior n r m ν) hlarge I hI hφ hchild
    (by simpa only [movingTemplateDoubledPrior_side] using hgap)
    (by simpa only [movingTemplateDoubledPrior_side] using hRH) hcomp]
  simp only [movingTemplateDoubledPrior_side]
  unfold movingAmplitudeOffDiagonal
  dsimp only [movingAmplitudePrior]
  have hr := amplitude_full_sum
    (U := TreeLeafIndex n × Fin 4 → σ) (S := transferFrequencyRange (V (n + 1)))
    (A := Pg) (B := MovingRegularSlot n r m → σ) (C := transferFrequencyRange (V n))
    (fun u => (((∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) : ℝ) : ℂ))
    ρ (fun y => ∏ i, ν i (y i))
    (fun u s XL XR left right v w => movingTemplateIntegerFourierTerm value outside μ
      childBound pivotBound V F φ G n r m I XL XR s.val left right greg ggiant favorable
        u v.val w.val)
  convert hr using 1
  simp only [Nat.cast_prod]

end Ostmann

end OAI
