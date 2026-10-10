import OAI.NumberTheory.Ostmann.Construction.InitialMovingSlots
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSpectatorHistory

namespace OAI

/-! # Exact spectator cofactors in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- A sum-indexed transform splits without any coprimality assumption. -/
theorem movingRegularTransform_sum {I J : Type*} [Fintype I] [Fintype J]
    (p : I ⊕ J → ℕ) [∀ i, NeZero (p i)] (g : ∀ i, ZMod (p i) → ℂ)
    (D : ℕ) (s : ℤ) :
    movingRegularTransform p g D s =
      movingRegularTransform (fun i => p (.inl i)) (fun i => g (.inl i))
        (D * ∏ j, p (.inr j)) s *
      movingRegularTransform (fun j => p (.inr j)) (fun j => g (.inr j))
        (D * ∏ i, p (.inl i)) s := by
  let L : I → ℕ := fun i => p (.inl i)
  let R : J → ℕ := fun j => p (.inr j)
  have hp : p = Sum.elim L R := by funext i; cases i <;> rfl
  unfold movingRegularTransform
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hc : tupleCofactor p (.inl i) = tupleCofactor L i * ∏ j, R j := by
      rw [hp, tupleCofactor_sum_left L R i (NeZero.ne (p (.inl i)))]
    have hm : D * (tupleCofactor L i * ∏ j, R j) =
        (D * ∏ j, R j) * tupleCofactor L i := by ring
    rw [hc, hm]
  · apply Finset.prod_congr rfl
    intro j _
    have hc : tupleCofactor p (.inr j) = (∏ i, L i) * tupleCofactor R j := by
      rw [hp, tupleCofactor_sum_right L R j (NeZero.ne (p (.inr j)))]
    rw [hc, ← mul_assoc]

/-- Reindexing a full original tuple separates exactly the fixed spectators
from the retained primes, including both original CRT cofactors. -/
theorem primeTupleFourierCoefficient_split {I J : Type*} [Fintype I] [Fintype J]
    {n : ℕ} (e : I ⊕ J ≃ Fin n) (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (F : Fin n → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ) (x : Fin n → P) :
    primeTupleFourierCoefficient P F ψ X V x =
      ∑ v ∈ transferFrequencyRange V,
        normalizedFourierProfile (fun t => 𝓕 ψ t) v ((∏ i, (x i : ℕ)) / X) *
          (movingRegularTransform (fun i => (x (e (.inl i)) : ℕ))
            (fun i => densityFourier (F (e (.inl i)) (x (e (.inl i)))))
            (∏ j, (x (e (.inr j)) : ℕ)) v *
          movingRegularTransform (fun j => (x (e (.inr j)) : ℕ))
            (fun j => densityFourier (F (e (.inr j)) (x (e (.inr j)))))
            (∏ i, (x (e (.inl i)) : ℕ)) v) := by
  unfold primeTupleFourierCoefficient
  apply Finset.sum_congr rfl
  intro v _
  rw [← movingRegularTransform_equiv e]
  rw [movingRegularTransform_sum]
  simp only [one_mul]

/-- A regular spectator block factors from the tagged giant/regular block. -/
theorem movingTaggedTransform_spectator_split {I J : Type*} [Fintype I] [Fintype J]
    (q : I → ℕ) (p : J → ℕ) (hq : ∀ i, q i ≠ 0) (hp : ∀ j, p j ≠ 0)
    (tag : J → Bool) (g h : ∀ q : ℕ, ZMod q → ℂ) (fav : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (Sum.elim q p) (Sum.elim (fun _ => false) tag) g h fav D s =
      (∏ i, g (q i) ((s : ZMod (q i)) * ((D * (∏ j, p j) * tupleCofactor q i : ℕ) : ZMod (q i))⁻¹)) *
        movingTaggedTransform p tag g h fav (D * ∏ i, q i) s := by
  unfold movingTaggedTransform
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_left q p i (hq i)]
    simp only [Sum.elim_inl, Bool.false_eq_true, ↓reduceIte]
    have hm : D * (tupleCofactor q i * ∏ j, p j) =
        (D * ∏ j, p j) * tupleCofactor q i := by ring
    rw [hm]
    rfl
  · apply Finset.prod_congr rfl
    intro j _
    rw [tupleCofactor_sum_right q p j (hp j)]
    simp only [Sum.elim_inr]
    rw [← mul_assoc]
    rfl

/-- The fixed spectator units are their true cofactors in the spectator list. -/
noncomputable def initialSpectatorCofactor {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : I) :
    (ZMod (q i))ˣ :=
  ZMod.unitOfCoprime (tupleCofactor q i) (tupleCofactor_coprime q hc i)

theorem initialSpectatorCofactor_val {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : I) :
    (initialSpectatorCofactor q hc i : ZMod (q i)) = (tupleCofactor q i : ℕ) := by
  simp only [initialSpectatorCofactor, ZMod.coe_unitOfCoprime]

/-- This is precisely the spectator leaf used throughout the moving recursion. -/
theorem initial_spectator_transform {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (g : ∀ i, ZMod (q i) → ℂ) (M : ℕ) (s : ℤ) :
    movingRegularTransform q g M s =
      ∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (g i)
        (initialSpectatorCofactor q hc i) () s := by
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  simp only [spectatorHistoryLeaf, initialSpectatorCofactor_val,
    Nat.cast_mul, div_eq_mul_inv]
  rw [mul_comm (M : ZMod (q i))]

end Ostmann

end OAI
