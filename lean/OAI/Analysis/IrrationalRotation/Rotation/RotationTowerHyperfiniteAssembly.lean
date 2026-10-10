import OAI.Analysis.IrrationalRotation.Rotation.RotationTowerCyclicApproximation
import OAI.Analysis.IrrationalRotation.Rotation.TowerDiagonalApproximation
import OAI.Analysis.IrrationalRotation.Rotation.RotationHyperfiniteCriterion

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.Rotation

theorem isHyperfinite_of_monotone_tower_partitions
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)] (θ : ℝ)
    (s : ∀ n, κ n → Set Circle) (hs : ∀ n b, MeasurableSet (s n b))
    (height : ∀ n, κ n → ℕ)
    (hdisj : ∀ n, Pairwise (fun a b : Σ c, Fin (height n c + 1) =>
      Disjoint (towerLevel θ (s n a.1) a.2) (towerLevel θ (s n b.1) b.2)))
    (hcover : ∀ n (x : Circle), ∃ b, ∃ i : Fin (height n b + 1),
      x ∈ towerLevel θ (s n b) i)
    (hheight : ∀ n b, n + 1 ≤ height n b + 1)
    (base : ℕ → Set Circle) (hsub : ∀ n b, s n b ⊆ base n)
    (hbase : ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ x ∈ base n, ∀ y ∈ base n, dist x y < δ)
    (hmono : Monotone (fun n => finiteTowerAlgebra θ (s n) (hs n)
      (fun b => height n b + 1))) : IsHyperfinite (algebra θ) := by
  classical
  let A := fun n => finiteTowerAlgebra θ (s n) (hs n) (fun b => height n b + 1)
  let ι := fun n => Σ b, Fin (height n b + 1)
  let level : ∀ n, ι n → Set Circle := fun n a => towerLevel θ (s n a.1) a.2
  have hm : ∀ n a, MeasurableSet (level n a) := fun n a =>
    measurableSet_towerLevel θ (s n a.1) (hs n a.1) a.2
  have hp : ∀ n x, ∃! a, x ∈ level n a := by
    intro n x
    obtain ⟨b, i, hi⟩ := hcover n x
    refine ⟨⟨b, i⟩, hi, ?_⟩
    intro a ha
    by_contra hne
    exact Set.disjoint_left.mp (hdisj n hne) ha hi
  have hA : ∀ n a, setProjection θ (level n a) (hm n a) ∈ A n := by
    intro n a
    rw [← towerMatrixEntries_diagonal_eq_setProjection θ (s n) (hs n)
      (fun b => height n b + 1) a.1 a.2]
    exact towerEntry_mem_finiteTowerAlgebra θ (s n) (hs n) _ a.1 a.2.isLt a.2.isLt
  obtain ⟨v, hv, _hvn, _hvnorm, hvstrong⟩ :=
    TowerDiagonalApproximation.exists_contractive_V_approximants_of_tower_levels
      ι θ level hm hp base (fun n a => s n a.1) (fun n a => (a.2.val : ℤ))
      (fun n a => hsub n a.1) (fun _ _ => rfl) hbase A hA
  apply isHyperfinite_of_strong_generator_sequences θ A hmono
    (fun n => finiteTowerAlgebra_le θ (s n) (hs n) _)
    (fun n => finiteTowerAlgebra_finiteDimensional θ (s n) (hs n) _ (hdisj n))
    (fun n => towerCyclicOperator θ (s n) (hs n) (height n)) v
    (fun n => (towerCyclicOperator_properties θ (s n) (hs n) (height n)
      (hdisj n) (hcover n)).1) hv
    (towerCyclicOperator_tendsto_apply κ θ s hs height hdisj hcover hheight) hvstrong

theorem isHyperfinite_of_refining_tower_partitions
    (κ τ : ℕ → Type*) [∀ n, Fintype (κ n)] (θ : ℝ)
    (s : ∀ n, κ n → Set Circle) (hs : ∀ n b, MeasurableSet (s n b))
    (height : ∀ n, κ n → ℕ)
    (hdisj : ∀ n, Pairwise (fun a b : Σ c, Fin (height n c + 1) =>
      Disjoint (towerLevel θ (s n a.1) a.2) (towerLevel θ (s n b.1) b.2)))
    (hcover : ∀ n (x : Circle), ∃ b, ∃ i : Fin (height n b + 1),
      x ∈ towerLevel θ (s n b) i)
    (hheight : ∀ n b, n + 1 ≤ height n b + 1)
    (base : ℕ → Set Circle) (hsub : ∀ n b, s n b ⊆ base n)
    (hbase : ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ x ∈ base n, ∀ y ∈ base n, dist x y < δ)
    (pieces : ∀ n, κ n → Finset (τ n))
    (index : ∀ n, κ n → τ n → κ (n + 1))
    (offset : ∀ n, κ n → τ n → ℕ)
    (hpiecesDisjoint : ∀ n b a, a ∈ pieces n b → ∀ a', a' ∈ pieces n b → a ≠ a' →
      Disjoint (towerLevel θ (s (n + 1) (index n b a)) (offset n b a))
        (towerLevel θ (s (n + 1) (index n b a')) (offset n b a')))
    (hpiecesCover : ∀ n b, s n b = ⋃ a ∈ pieces n b,
      towerLevel θ (s (n + 1) (index n b a)) (offset n b a))
    (hfit : ∀ n b a, a ∈ pieces n b →
      offset n b a + (height n b + 1) ≤ height (n + 1) (index n b a) + 1) :
    IsHyperfinite (algebra θ) := by
  apply isHyperfinite_of_monotone_tower_partitions κ θ s hs height hdisj hcover
    hheight base hsub hbase
  apply monotone_nat_of_le_succ
  intro n
  exact finiteTowerAlgebra_le_of_set_refinement θ (s n) (s (n + 1)) (hs n) (hs (n + 1))
    (fun b => height n b + 1) (fun b => height (n + 1) b + 1)
    (pieces n) (index n) (offset n) (hpiecesDisjoint n) (hpiecesCover n) (hfit n)

end Invariant233.Rotation

end

end OAI
