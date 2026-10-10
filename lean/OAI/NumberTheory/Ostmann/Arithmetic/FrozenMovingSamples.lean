import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleValues

namespace OAI

/-! # The actual low-tier samples stay fixed when bulk slots vary -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, v i = w i) :
    movingSlotValues v n small = movingSlotValues w n small := by
  induction n with
  | zero =>
    unfold movingSlotValues MovingSlotReversal.naturalProduct
    congr 1
    exact List.map_congr_left h
  | succ n ih =>
    exact Prod.ext
      (ih small.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih small.2 (fun i hi => h i (List.mem_append_right _ hi)))

theorem movingCompensationValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n)
    (h : ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n samples), v i = w i) :
    movingCompensationValues v n samples = movingCompensationValues w n samples := by
  induction n with
  | zero =>
    funext i
    apply h
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  | succ n ih =>
    exact Prod.ext
      (ih samples.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih samples.2 (fun i hi => h i (List.mem_append_right _ hi)))

/-- All internal samples have lower tier than the current bulk. This proves
equality of the complete sampled tree, including its shared child samples. -/
theorem MovingSampleSlots.values_eq_of_levels {σ : Type*} (tier : σ → ℕ)
    (v w : σ → ℕ) (k : ℕ) (heq : ∀ i, tier i < k → v i = w i)
    {n : ℕ} (samples : MovingSampleSlots σ n) (hn : n ≤ k)
    (hlevels : samples.Levels tier) : samples.values v = samples.values w := by
  induction samples with
  | leaf => rfl
  | @node n s left right ihL ihR =>
    change MovingGiantSamples.node (movingCompensationValues v n s) (left.values v) (right.values v) =
      MovingGiantSamples.node (movingCompensationValues w n s) (left.values w) (right.values w)
    congr 1
    · apply movingCompensationValues_congr
      intro i hi
      apply heq
      rw [hlevels.1 i hi]
      omega
    · exact ihL (by omega) hlevels.2.1
    · exact ihR (by omega) hlevels.2.2

/-- Replacing precisely the selected bulk coordinates preserves both sources
of nonbulk data used to construct the field diagram. -/
theorem frozenMoving_nonbulk_values {σ J : Type*} (tier : σ → ℕ)
    (base value : σ → ℕ) (e : J ↪ σ) (n : ℕ)
    (he : ∀ j, n ≤ tier (e j))
    (hv : ∀ i ∉ Set.range e, value i = base i)
    (small : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range e)
    (hsamples : samples.Levels tier) :
    movingSlotValues value n small = movingSlotValues base n small ∧
      samples.values value = samples.values base := by
  refine ⟨movingSlotValues_congr value base n small (fun i hi => hv i (hsmall i hi)), ?_⟩
  apply samples.values_eq_of_levels tier value base n _ (le_refl _) hsamples
  intro i hi
  apply hv
  rintro ⟨j, rfl⟩
  exact (not_lt_of_ge (he j)) hi

end Ostmann

end OAI
