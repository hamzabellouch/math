import OAI.NumberTheory.Ostmann.Arithmetic.MovingFirstExtendedWindows

namespace OAI

/-! # The first recursive product bound from the two original windows -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Nonzero first-level coefficients retain both terminal windows. Removing the
shared inner pivot from each gives a bound on the full current product. -/
theorem movingFrequencyCoefficient_one_product_bound {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi lower : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hmin : ∀ a : Fin 4 → σ, movingCompensationPrior (μ 0) 0 a ≠ 0 →
      ∀ p : ℕ, 0 < p → φ (Real.log p - G 1) ≠ 0 →
        lower ≤ (p * MovingSlotReversal.naturalProduct value (List.ofFn a) : ℕ))
    (H : ℕ) (hcap : X * hi ≤ lower * H)
    (s : ℤ)
    (small bulk : List σ × List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 1 s small bulk XL XR ≠ 0) :
    (XL * MovingSlotReversal.naturalProduct value (small.1 ++ bulk.1)) *
      (XR * MovingSlotReversal.naturalProduct value (small.2 ++ bulk.2)) ≤ H ^ 2 := by
  obtain ⟨a, v, w, hm, hp, hU, hphi, hl, hr⟩ :=
    movingFrequencyCoefficient_one_extended_children value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G s small bulk XL XR h
  let p := movingTopPivot value (small.1 ++ bulk.1) (small.2 ++ bulk.2)
    (List.ofFn a) XL XR s v.val w.val
  have hlow := hmin a hm p hp hphi
  have hleft := movingFrequencyCoefficient_initial_retained_bound value outside μ
    childBound pivotBound V q F g Dq S ψ X lo hi lower hX φ G v.val (List.ofFn a)
    small.1 bulk.1 p XL H hp hU hlow hcap hl
  have hright := movingFrequencyCoefficient_initial_retained_bound value outside μ
    childBound pivotBound V q F g Dq S ψ X lo hi lower hX φ G w.val (List.ofFn a)
    small.2 bulk.2 p XR H hp hU hlow hcap hr
  simpa only [pow_two] using Nat.mul_le_mul hleft hright

theorem movingFrequencyCoefficient_one_retained_bound {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi lower : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hmin : ∀ a : Fin 4 → σ, movingCompensationPrior (μ 0) 0 a ≠ 0 →
      ∀ p : ℕ, 0 < p → φ (Real.log p - G 1) ≠ 0 →
        lower ≤ (p * MovingSlotReversal.naturalProduct value (List.ofFn a) : ℕ))
    (H : ℕ) (hcap : X * hi ≤ lower * H)
    (s : ℤ)
    (comp small bulk : List σ × List σ) (XL XR K : ℕ)
    (hp : 0 < XL)
    (hcomp : 0 < MovingSlotReversal.naturalProduct value (comp.1 ++ comp.2))
    (outerLower : ℝ)
    (houter : outerLower ≤ (XL * MovingSlotReversal.naturalProduct value (comp.1 ++ comp.2) : ℕ))
    (hK : ((H ^ 2 : ℕ) : ℝ) ≤ outerLower * K)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 1 s (comp.1 ++ small.1, comp.2 ++ small.2) bulk XL XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value
      ((small.1 ++ bulk.1) ++ (small.2 ++ bulk.2)) ≤ K := by
  have hb := movingFrequencyCoefficient_one_product_bound value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi lower hX φ G hmin H hcap s
    (comp.1 ++ small.1, comp.2 ++ small.2) bulk XL XR h
  have hid :
      (XL * MovingSlotReversal.naturalProduct value ((comp.1 ++ small.1) ++ bulk.1)) *
        (XR * MovingSlotReversal.naturalProduct value ((comp.2 ++ small.2) ++ bulk.2)) =
      (XL * MovingSlotReversal.naturalProduct value (comp.1 ++ comp.2)) *
        (XR * MovingSlotReversal.naturalProduct value
          ((small.1 ++ bulk.1) ++ (small.2 ++ bulk.2))) := by
    simp only [movingNaturalProduct_append]
    ring
  change (XL * MovingSlotReversal.naturalProduct value ((comp.1 ++ small.1) ++ bulk.1)) *
    (XR * MovingSlotReversal.naturalProduct value ((comp.2 ++ small.2) ++ bulk.2)) ≤ H ^ 2 at hb
  rw [hid] at hb
  have hbR : ((XL * MovingSlotReversal.naturalProduct value (comp.1 ++ comp.2) : ℕ) : ℝ) *
      (XR * MovingSlotReversal.naturalProduct value
        ((small.1 ++ bulk.1) ++ (small.2 ++ bulk.2)) : ℕ) ≤ ((H ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hb
  have hcR : (0 : ℝ) < (XL * MovingSlotReversal.naturalProduct value (comp.1 ++ comp.2) : ℕ) := by
    exact_mod_cast Nat.mul_pos hp hcomp
  have ht := hbR.trans (hK.trans (mul_le_mul_of_nonneg_right houter (Nat.cast_nonneg K)))
  exact_mod_cast (mul_le_mul_iff_right₀ hcR).mp ht

end Ostmann

end OAI
