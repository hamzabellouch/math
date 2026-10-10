import OAI.NumberTheory.Ostmann.Arithmetic.MovingGuardedDirectRecursion
import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyHistory

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

/-- The root frequency is fixed by the amplitude; only its descendants are
summed here, each under its own level cutoff. -/
def MovingDescendantFrequencyIndex (V : ℕ → ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n

instance movingDescendantFrequencyIndexFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (MovingDescendantFrequencyIndex V n) := by
  cases n <;> dsimp only [MovingDescendantFrequencyIndex] <;> infer_instance

noncomputable def movingRootedFrequencyTree (V : ℕ → ℕ) :
    (n : ℕ) → ℤ → MovingDescendantFrequencyIndex V n → FrequencyTree ℤ n
  | 0, s, _ => s
  | n + 1, s, t => (s, scheduledFrequencyHistory V n t.1, scheduledFrequencyHistory V n t.2)

def scheduledFrequencyRootEquiv (V : ℕ → ℕ) (n : ℕ) :
    ScheduledFrequencyIndex V n ≃ transferFrequencyRange (V n) × MovingDescendantFrequencyIndex V n := by
  cases n with
  | zero => exact (Equiv.prodUnique _ Unit).symm
  | succ n => exact Equiv.refl _

theorem scheduledFrequencyRootEquiv_history (V : ℕ → ℕ) (n : ℕ)
    (t : ScheduledFrequencyIndex V n) :
    scheduledFrequencyHistory V n t =
      movingRootedFrequencyTree V n (scheduledFrequencyRootEquiv V n t).1.val
        (scheduledFrequencyRootEquiv V n t).2 := by
  cases n <;> rfl

/-- The original root sum can be reindexed without counting a root twice. -/
theorem scheduledFrequency_sum_rooted (V : ℕ → ℕ) (n : ℕ)
    (f : FrequencyTree ℤ n → ℂ) :
    (∑ t : ScheduledFrequencyIndex V n, f (scheduledFrequencyHistory V n t)) =
      ∑ s : transferFrequencyRange (V n), ∑ t : MovingDescendantFrequencyIndex V n,
        f (movingRootedFrequencyTree V n s.val t) := by
  have he := (scheduledFrequencyRootEquiv V n).sum_comp
    (fun t => f (movingRootedFrequencyTree V n t.1.val t.2))
  simp_rw [← scheduledFrequencyRootEquiv_history] at he
  rw [Fintype.sum_prod_type] at he
  exact he

/-- This is the current coefficient after the original internal prime samples
and all descendant frequencies have been summed. Root guards remain in each
term and are never turned into a conditioned probability law. -/
noncomputable def movingFrequencyCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ t : MovingDescendantFrequencyIndex V n,
    movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n
      (movingRootedFrequencyTree V n s t) small bulk XL XR

/-- At a successor level the two child histories are independent finite
indices, while each root compensation vector is shared exactly once. -/
theorem movingFrequencyCoefficient_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) s small bulk XL XR =
      ∑ l : ScheduledFrequencyIndex V n, ∑ r : ScheduledFrequencyIndex V n,
        ∑ a : TreeLeafTuple (Fin 4 → σ) n,
          let u := movingCompensationSlots n a
          let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
          let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
          let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
          let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
          let U := x.compensation value
          let v := frequencyRoot n t.2.1
          let w := frequencyRoot n t.2.2
          let p := reconstructedPivot
            (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (s * U)
          (movingCompensationPrior (μ n) n a : ℂ) *
            if movingLocalSupport value outside x ∧
                (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
                  0 < U) then
              (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
                movingSupportedSampledWeight value outside μ childBound pivotBound F
                  (movingOriginalNode value childBound pivotBound φ G) n t.2.1
                  (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
                star (movingSupportedSampledWeight value outside μ childBound pivotBound F
                  (movingOriginalNode value childBound pivotBound φ G) n t.2.2
                  (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
            else 0 := by
  unfold movingFrequencyCoefficient
  change (∑ t : ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  exact movingSupportedSampledWeight_direct_node value outside μ childBound pivotBound F φ G n
    (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r) small bulk XL XR

/-- Identification with the already proved original prime-pattern expansion.
This links the finite frequency coefficient to the arithmetic comparison. -/
theorem movingFrequencyCoefficient_original {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR =
      ∑ t : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
          n (movingRootedFrequencyTree V n s t) small bulk XL XR := by
  simp only [movingFrequencyCoefficient, movingOriginalSampleAverage_eq]

/-- The frequency square has exactly two independent descendant histories.
In particular no bound by the number of histories has been used here. -/
theorem movingFrequencyCoefficient_square {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    ‖movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s small bulk XL XR‖ ^ 2 =
      (∑ t : MovingDescendantFrequencyIndex V n, ∑ u : MovingDescendantFrequencyIndex V n,
        movingSupportedSampledWeight value outside μ childBound pivotBound F
          (movingOriginalNode value childBound pivotBound φ G) n
          (movingRootedFrequencyTree V n s t) small bulk XL XR *
        star (movingSupportedSampledWeight value outside μ childBound pivotBound F
          (movingOriginalNode value childBound pivotBound φ G) n
          (movingRootedFrequencyTree V n s u) small bulk XL XR)).re := by
  rw [movingFrequencyCoefficient]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Complex.star_def]
  rw [← map_sum (starRingEnd ℂ), Complex.mul_conj']
  norm_cast

end Ostmann

end OAI
