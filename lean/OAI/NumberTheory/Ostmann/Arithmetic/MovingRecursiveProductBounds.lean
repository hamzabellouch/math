import OAI.NumberTheory.Ostmann.Arithmetic.MovingEarlyCellCaps
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularSlots

namespace OAI

/-! # Product windows inherited through every actual integer extension -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The logarithmic product budget left after each common pivot is removed. -/
noncomputable def movingProductExponent (T : ℕ → ℝ) (W : ℝ) : ℕ → ℝ
  | 0 => W
  | n + 1 => 2 * (movingProductExponent T W n - T n)

private theorem remove_positive_product (A B : ℕ) (T E : ℝ)
    (hA : Real.exp T ≤ (A : ℝ)) (hAB : ((A * B : ℕ) : ℝ) ≤ Real.exp E) :
    (B : ℝ) ≤ Real.exp (E - T) := by
  rw [Nat.cast_mul] at hAB
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos T)).mpr
  have hh := (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg B)).trans hAB
  simpa only [Nat.cast_mul, mul_comm] using hh

theorem movingNaturalProduct_append_leaves {σ : Type*} (value : σ → ℕ)
    (n : ℕ) (u small bulk : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (appendMovingSlotLeaves n u small) ++ flattenMovingSlots n bulk) =
      MovingSlotReversal.naturalProduct value (flattenMovingSlots n u) *
        MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  have hp := ((flattenMovingSlots_append_perm n u small).append_right
    (flattenMovingSlots n bulk)).map value
  change (List.map value _).prod = _
  rw [hp.prod_eq]
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
  ring

/-- This bound is proved on the original sampled histories, before summing any
frequencies. The inserted giants may be arbitrary positive integers. -/
theorem movingSupportedSampledWeight_product_bound {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (T : ℕ → ℝ) (W : ℝ)
    (hF : ∀ s small XL XR,
      F ⟨0, .leaf s small, XL, XR⟩ s ≠ 0 →
        ((XL * XR * MovingSlotReversal.naturalProduct value small : ℕ) : ℝ) ≤ Real.exp W)
    (hmin : ∀ n (a : TreeLeafTuple (Fin 4 → σ) n),
      movingCompensationPrior (μ n) n a ≠ 0 → ∀ p : ℕ, 0 < p →
      φ (Real.log p - G (n + 1)) ≠ 0 →
      Real.exp (T n) ≤ (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ))
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR ≠ 0) :
    ((XL * XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) : ℕ) : ℝ) ≤
        Real.exp (movingProductExponent T W n) := by
  induction n generalizing XL XR with
  | zero =>
    change List σ at small bulk
    change ℤ at t
    have hh := movingFrequencyCoefficient_levelZero_support σ value outside μ childBound pivotBound
      (fun _ => 0) F φ G t small bulk XL XR
      (by rwa [movingFrequencyCoefficient_levelZero_sample])
    exact hF t (small ++ bulk) XL XR hh
  | succ n ih =>
    rw [movingSupportedSampledWeight_direct_node] at h
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    dsimp only at ha
    have hm : movingCompensationPrior (μ n) n a ≠ 0 := by
      intro hz
      exact ha (by rw [hz, Complex.ofReal_zero, zero_mul])
    have hb := right_ne_zero_of_mul ha
    split_ifs at hb with hg
    · let u := movingCompensationSlots n a
      let p := movingTopPivot value
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
        (flattenMovingSlots n u) XL XR t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      have hp : 0 < p := Nat.pos_of_mul_pos_right hg.2.1.pivot_pos
      have hphi : φ (Real.log p - G (n + 1)) ≠ 0 := by
        intro hz
        apply left_ne_zero_of_mul (left_ne_zero_of_mul hb)
        change (((MovingSlotReversal.naturalProduct value (flattenMovingSlots n u) : ℝ) *
          φ (Real.log p - G (n + 1)) : ℝ) : ℂ) = 0
        rw [hz, mul_zero, Complex.ofReal_zero]
      have hl := ih t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 p XL
        (right_ne_zero_of_mul (left_ne_zero_of_mul hb))
      have hr := ih t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 p XR
        (star_ne_zero.mp (right_ne_zero_of_mul hb))
      rw [movingNaturalProduct_append_leaves] at hl hr
      let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
      let L := XL * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      let R := XR * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      have hidL : p * XL * (U * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)) = (p * U) * L := by
        dsimp only [L]; ring
      have hidR : p * XR * (U * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)) = (p * U) * R := by
        dsimp only [R]; ring
      rw [hidL] at hl
      rw [hidR] at hr
      have hlow := hmin n a hm p hp hphi
      have hl' := remove_positive_product (p * U) L (T n) _ hlow hl
      have hr' := remove_positive_product (p * U) R (T n) _ hlow hr
      have hprod := mul_le_mul hl' hr' (Nat.cast_nonneg R) (Real.exp_nonneg _)
      have hid : XL * XR * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots (n + 1) small ++ flattenMovingSlots (n + 1) bulk) = L * R := by
        simp only [flattenMovingSlots, movingNaturalProduct_append, L, R]
        ring
      rw [hid, Nat.cast_mul]
      convert hprod using 1
      rw [movingProductExponent, ← Real.exp_add]
      congr 1
      ring
    · exact (hb rfl).elim

/-- Summing descendants cannot create support outside the inherited product
window. This is the coefficient used by the original arithmetic comparison. -/
theorem movingFrequencyCoefficient_recursive_product_bound {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X) (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G T : ℕ → ℝ)
    (hmin : ∀ n (a : TreeLeafTuple (Fin 4 → σ) n),
      movingCompensationPrior (μ n) n a ≠ 0 → ∀ p : ℕ, 0 < p →
      φ (Real.log p - G (n + 1)) ≠ 0 →
      Real.exp (T n) ≤ (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ))
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR ≠ 0) :
    ((XL * XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) : ℕ) : ℝ) ≤
        Real.exp (movingProductExponent T W n) := by
  unfold movingFrequencyCoefficient at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  apply movingSupportedSampledWeight_product_bound value outside μ childBound pivotBound
    (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G T W _ hmin n _ small bulk XL XR ht
  intro s small XL XR hh
  have hw := movingOriginalLeaf_window value q F g Dq S ψ X lo hi
    ⟨0, .leaf s small, XL, XR⟩ s hh
  have hu := (div_le_iff₀ hX).mp hw.2
  have hu' : ((XL * XR * MovingSlotReversal.naturalProduct value small : ℕ) : ℝ) ≤ X * hi := by
    simpa only [movingSlotModulus, mul_comm] using hu
  exact hu'.trans hwindow

end Ostmann

end OAI
