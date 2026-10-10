import OAI.Analysis.IrrationalRotation.Analysis.RecursiveReturnTowerFits
import OAI.Analysis.IrrationalRotation.Rotation.RotationTowerHyperfiniteAssembly

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.Rotation

theorem addRight_iterate_eq_action (θ : ℝ) (n : ℕ) (x : Circle) :
    ((MeasurableEquiv.addRight (θ : Circle) : Circle → Circle)^[n]) x =
      action θ (n : ℤ) x := by
  induction n with
  | zero => simp [action]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change (x + (n : ℤ) • (θ : Circle)) + (θ : Circle) =
      x + ((n + 1 : ℕ) : ℤ) • (θ : Circle)
    simp [Nat.cast_add, add_zsmul, add_assoc]

theorem returnTower_level_eq_towerLevel (θ : ℝ)
    (P : FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)))
    (a : P.LevelIndex) :
    P.level a = towerLevel θ (P.base a.1) a.2.val := by
  unfold FiniteReturnTower.level TowerItinerary.indexedLevel TowerItinerary.level towerLevel
  congr 1
  funext x
  exact addRight_iterate_eq_action θ a.2.val x

theorem recursive_finiteTowerAlgebra_monotone (θ : ℝ)
    (raw : ℕ → FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)))
    (hnest : ∀ n, (raw (n + 1)).returnBase ⊆ (raw n).returnBase) :
    Monotone (fun n => finiteTowerAlgebra θ
      (FiniteReturnTower.sequence raw n).base
      (FiniteReturnTower.sequence raw n).base_measurable
      (FiniteReturnTower.sequence raw n).height) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  apply finiteTowerAlgebra_le_of_set_refinement θ
    (FiniteReturnTower.sequence raw n).base
    (FiniteReturnTower.sequence raw (n + 1)).base
    (FiniteReturnTower.sequence raw n).base_measurable
    (FiniteReturnTower.sequence raw (n + 1)).base_measurable
    (FiniteReturnTower.sequence raw n).height
    (FiniteReturnTower.sequence raw (n + 1)).height
    (FiniteReturnTower.successorBaseLevels raw n)
    (fun _ a => a.1) (fun _ a => a.2.val)
  · intro b a ha a' ha' hne
    simpa only [← returnTower_level_eq_towerLevel] using
      (FiniteReturnTower.sequence raw (n + 1)).disjoint hne
  · intro b
    simpa only [returnTower_level_eq_towerLevel] using
      FiniteReturnTower.sequence_base_eq_successor_fitting_union raw hnest n b
  · intro b a ha
    exact FiniteReturnTower.sequence_successorBaseLevels_fits raw n b a ha

theorem isHyperfinite_of_raw_return_towers (θ : ℝ)
    (raw : ℕ → FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)))
    (hnest : ∀ n, (raw (n + 1)).returnBase ⊆ (raw n).returnBase)
    (hheight : ∀ n i, n + 1 ≤ (raw n).height i)
    (hmesh : ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ x ∈ (raw n).returnBase, ∀ y ∈ (raw n).returnBase, dist x y < δ) :
    IsHyperfinite (algebra θ) := by
  classical
  let P := FiniteReturnTower.sequence raw
  have hrec (n : ℕ) (i : (P n).Index) :
      (P n).height i - 1 + 1 = (P n).height i :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (ne_of_gt ((P n).height_pos i)))
  apply isHyperfinite_of_monotone_tower_partitions
    (fun n => (P n).Index) θ (fun n => (P n).base)
    (fun n => (P n).base_measurable) (fun n i => (P n).height i - 1)
    (base := fun n => (raw n).returnBase)
  · intro n a b hab
    let e : (Σ c, Fin ((P n).height c - 1 + 1)) ≃ (P n).LevelIndex :=
      Equiv.sigmaCongrRight (fun c => finCongr (hrec n c))
    have hne : e a ≠ e b := fun h => hab (e.injective h)
    have hd := (P n).disjoint hne
    simpa only [returnTower_level_eq_towerLevel, e, Equiv.sigmaCongrRight_apply,
      finCongr_apply, Fin.val_cast] using hd
  · intro n x
    obtain ⟨b, i, hi⟩ := (P n).covers x
    refine ⟨b, Fin.cast (hrec n b).symm i, ?_⟩
    change x ∈ (P n).level ⟨b, i⟩ at hi
    simpa only [returnTower_level_eq_towerLevel, Fin.val_cast] using hi
  · intro n i
    rw [hrec]
    exact (FiniteReturnTower.sequence_height_parent raw n i).symm ▸
      hheight n (FiniteReturnTower.sequenceParent raw n i)
  · intro n i x hx
    have hm : x ∈ (P n).returnBase := by
      rw [← (P n).bases_cover]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa only [P, FiniteReturnTower.sequence_returnBase] using hm
  · exact hmesh
  · simpa only [hrec] using recursive_finiteTowerAlgebra_monotone θ raw hnest

end Invariant233.Rotation

end

end OAI
