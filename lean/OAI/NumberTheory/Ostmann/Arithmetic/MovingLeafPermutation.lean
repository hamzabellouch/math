import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialCoefficient

namespace OAI

/-! # Reordering the regular primes in an original terminal leaf -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLocalSupport_leaf_perm {A : Type*} (value : A → ℕ)
    (outside : List ℕ) (L R : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingLocalSupport value outside ⟨0, .leaf s L, XL, XR⟩ ↔
      movingLocalSupport value outside ⟨0, .leaf s R, XL, XR⟩ := by
  have hp : MovingSlotReversal.naturalProduct value L =
      MovingSlotReversal.naturalProduct value R := (h.map value).prod_eq
  have hpair := (((h.map value).cons XR).cons XL).append_right outside
  have he : (XL :: XR :: L.map value ++ outside).Pairwise Nat.Coprime ↔
      (XL :: XR :: R.map value ++ outside).Pairwise Nat.Coprime :=
    hpair.pairwise_iff (fun h => h.symm)
  simp only [movingLocalSupport, MovingSlotData.currentSlots, MovingSlotData.regularSlots,
    movingLocalGiantUnits, MovingSlotData.frequencyProduct, List.cons_append, hp]
  exact and_congr_left (fun _ => by simpa only [List.cons_append] using he)

theorem movingOriginalLeaf_constant_leaf_perm {A I : Type*} (value : A → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (L R : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi ⟨0, .leaf s L, XL, XR⟩ s =
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi ⟨0, .leaf s R, XL, XR⟩ s := by
  have hp : MovingSlotReversal.naturalProduct value L =
      MovingSlotReversal.naturalProduct value R := (h.map value).prod_eq
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, movingFourierLeaf,
    movingSlotModulus, spectatorHistoryLeaf, hp]
  rfl

theorem movingFrequencyCoefficient_zero_small_perm {A I : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (L R bulk : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 s L bulk XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 s R bulk XL XR := by
  rw [movingFrequencyCoefficient_levelZero, movingFrequencyCoefficient_levelZero]
  unfold movingGuardedLeaf
  rw [movingLocalSupport_leaf_perm value outside (L ++ bulk) (R ++ bulk) (h.append_right bulk)]
  rw [movingOriginalLeaf_constant_leaf_perm value q f g Dq S ψ X lo hi
    (L ++ bulk) (R ++ bulk) (h.append_right bulk)]

end Ostmann

end OAI
