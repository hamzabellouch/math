import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePairExpansion

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalLeaf {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  (movingWindowLeaf value X lo hi (movingDataLeaf F) x s * movingFourierLeaf value ψ X x s) *
    ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s

noncomputable def movingOriginalNode {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    MovingSlotState σ → ℤ → ℤ → ℤ → ℝ :=
  movingPhiExtra value childBound pivotBound (fun _ _ _ _ => 1) φ G

theorem movingOriginalNode_local {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingLocalExtra (movingOriginalNode value childBound pivotBound φ G) =
      movingOriginalNode value childBound pivotBound φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingOriginalNode_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G) =
      movingPhiExtra value childBound pivotBound (movingDataExtra (movingCompensationExtra value)) φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [movingCompensatedExtra, movingOriginalNode, movingPhiExtra,
    movingDataExtra, movingCompensationExtra, MovingSlotState.compensation, Nat.cast_one, one_mul]

/-- The sampled Fourier coefficient, with all original support and all
original internal probabilities. -/
noncomputable def movingOriginalSampleAverage {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
    movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F (movingCompensationExtra value)
        g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR)

/-- The Fourier/window/spectator coefficient is exactly the local sampled
recursion already expanded above. -/
theorem movingOriginalSampleAverage_eq {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR =
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (movingOriginalLeaf value q F g Dq S ψ X lo hi)
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR := by
  unfold movingSupportedSampledWeight
  rw [movingSampledWeight_supported, movingLocalExtra_compensated, movingOriginalNode_local,
    movingOriginalNode_compensated]
  rfl

/-- After extracting compensation, the retained term is the original giant
coefficient with unit data at internal nodes. -/
theorem movingSupportedSampleTerm_original {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (a : MovingSampleSlots σ n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (movingOriginalLeaf value q F g Dq S ψ X lo hi)
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR a =
    movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
        g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR) := by
  unfold movingSupportedSampleTerm
  rw [movingOriginalNode_local]
  rfl

end Ostmann

end OAI
