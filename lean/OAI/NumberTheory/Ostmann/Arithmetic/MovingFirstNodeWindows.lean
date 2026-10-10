import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialCoefficient

namespace OAI

/-! # The first recursive node retains both original terminal windows -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingPrimeNodeFactor_support {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ)
    (h : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u
      XL XR s v w ≠ 0) :
    0 < movingTopPivot value CL CR u XL XR s v w ∧
      0 < MovingSlotReversal.naturalProduct value u ∧
      φ (Real.log (movingTopPivot value CL CR u XL XR s v w) - G (n + 1)) ≠ 0 := by
  unfold movingPrimeNodeFactor at h
  dsimp only at h
  split_ifs at h with hg
  · have hp : 0 < movingTopPivot value CL CR u XL XR s v w *
        MovingSlotReversal.naturalProduct value u := hg.2.1.2.2.2.1
    refine ⟨(Nat.pos_of_mul_pos_right hp), hg.2.2, ?_⟩
    intro hz
    exact h (by simp only [hz, mul_zero, Complex.ofReal_zero])
  · exact (h rfl).elim

theorem movingFrequencyCoefficient_one_children {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (hs : s ≠ 0) (hsV : s.natAbs ≤ V 1)
    (small bulk : List σ × List σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V 1 < XL) (hVR : V 1 < XR)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      1 s small bulk XL XR ≠ 0) :
    ∃ (a : Fin 4 → σ) (v w : transferFrequencyRange (V 0)),
      let u := List.ofFn a
      let CL := small.1 ++ bulk.1
      let CR := small.2 ++ bulk.2
      let p := movingTopPivot value CL CR u XL XR s v.val w.val
      movingCompensationPrior (μ 0) 0 a ≠ 0 ∧
      movingPrimeNodeFactor value outside childBound pivotBound φ G 0 CL CR u
        XL XR s v.val w.val ≠ 0 ∧
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 v.val
        (u ++ small.1) bulk.1 p XL ≠ 0 ∧
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 w.val
        (u ++ small.2) bulk.2 p XR ≠ 0 := by
  rw [movingFrequencyCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
    φ G 0 s hs hsV small bulk XL XR hXL hXR hVL hVR] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hprior : movingCompensationPrior (μ 0) 0 a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, Complex.ofReal_zero, zero_mul])
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul ha)
  obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine ⟨a, v, w, hprior, ?_, ?_, ?_⟩
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hw)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
  · exact star_ne_zero.mp (right_ne_zero_of_mul hw)

theorem movingFrequencyCoefficient_one_window_witness {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (hF : ∀ x, movingOriginalLeaf value q F g Dq S ψ X lo hi x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (hs : s ≠ 0) (hsV : s.natAbs ≤ V 1)
    (small bulk : List σ × List σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V 1 < XL) (hVR : V 1 < XR)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 1 s small bulk XL XR ≠ 0) :
    ∃ (a : Fin 4 → σ) (v w : transferFrequencyRange (V 0)),
      let u := List.ofFn a
      let CL := small.1 ++ bulk.1
      let CR := small.2 ++ bulk.2
      let p := movingTopPivot value CL CR u XL XR s v.val w.val
      movingCompensationPrior (μ 0) 0 a ≠ 0 ∧ 0 < p ∧
      0 < MovingSlotReversal.naturalProduct value u ∧
      φ (Real.log p - G 1) ≠ 0 ∧
      (X * lo ≤ (p * XL * MovingSlotReversal.naturalProduct value ((u ++ small.1) ++ bulk.1) : ℕ) ∧
        ((p * XL * MovingSlotReversal.naturalProduct value ((u ++ small.1) ++ bulk.1) : ℕ) : ℝ) ≤ X * hi) ∧
      (X * lo ≤ (p * XR * MovingSlotReversal.naturalProduct value ((u ++ small.2) ++ bulk.2) : ℕ) ∧
        ((p * XR * MovingSlotReversal.naturalProduct value ((u ++ small.2) ++ bulk.2) : ℕ) : ℝ) ≤ X * hi) := by
  obtain ⟨a, v, w, hm, hn, hl, hr⟩ := movingFrequencyCoefficient_one_children value outside μ
    childBound pivotBound V hV (movingOriginalLeaf value q F g Dq S ψ X lo hi) hF
    φ G s hs hsV small bulk XL XR hXL hXR hVL hVR h
  have hnode := movingPrimeNodeFactor_support value outside childBound pivotBound φ G 0
    (small.1 ++ bulk.1) (small.2 ++ bulk.2) (List.ofFn a) XL XR s v.val w.val hn
  refine ⟨a, v, w, hm, hnode.1, hnode.2.1, hnode.2.2, ?_, ?_⟩
  · exact movingFrequencyCoefficient_initial_window value outside μ childBound pivotBound V
      q F g Dq S ψ X lo hi hX φ G v.val _ _ _ _ hl
  · exact movingFrequencyCoefficient_initial_window value outside μ childBound pivotBound V
      q F g Dq S ψ X lo hi hX φ G w.val _ _ _ _ hr

end Ostmann

end OAI
