import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSampleExpansion

namespace OAI

/-! # Scalar multipliers in the original terminal coefficient -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalLeaf_mul {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (w : {n : ℕ} → MovingSlotData σ n → ℂ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ) :
    movingOriginalLeaf value q (fun T s => w T * F T s) g Dq S ψ X lo hi x s =
      w x.data * movingOriginalLeaf value q F g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  split <;> ring

theorem movingOriginalLeaf_zero {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q F g Dq S ψ X lo hi x 0 = 0 := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  split <;> simp only [hF, zero_mul]

end Ostmann

end OAI
