import OAI.GroupTheory.Thompson.TransportFamily
import OAI.GroupTheory.Thompson.FiniteCorrelationBoundary

namespace OAI

noncomputable section

universe uE

namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_fixed_boundary (f : UnitBall E → UnitBall E) (L δ : ℝ)
    (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ x y, ‖(f x : E) - f y‖ ≤ L * ‖(x : E) - y‖)
    (hDisp : ∀ x, δ ≤ ‖(f x : E) - x‖)
    (D : ℕ) (hD : 2 ≤ D) (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    ∃ S : Finset F, S.Nonempty ∧ 0 < boundaryConstant L δ D ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S, boundaryConstant L δ D ≤ boundaryRatio A h := by
  refine ⟨fixedTransportSet hD, fixedTransportSet_nonempty hD,
    boundaryConstant_pos hL hδ hD hlarge, ?_⟩
  intro A hA
  obtain ⟨n, hg, hhg⟩ := exists_transport_admissible hD A
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  let x : F → Fin D → UnitBall E := fun g i => globalColor hDpos f n (.inl i) g
  let y : F → Fin D → Fin D → UnitBall E :=
    fun g i j => globalColor hDpos f n (.inr (i, j)) g
  let α : ℝ := realAvg A (globalCorrelation hDpos f n
    (.inl (firstIndex hD)) (.inl (secondIndex hD)))
  let η : ℝ := boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A
  have hrec : ∀ g ∈ A, ∀ i, x g i = f (ballMean hDpos (y g i)) := by
    intro g hmem i
    exact globalColor_parent hDpos f n g (hg g hmem) i
  have hparent : ∀ j k, j ≠ k →
      |corr A (fun g => (x g j : E)) (fun g => (x g k : E)) - α| ≤ η := by
    intro j k hjk
    exact separated_correlation_bound hD f n A hA hg hhg (.inl j) (.inl k)
      (selectedInterval_separated hjk)
  have hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => (y g i j : E)) (fun g => (y g i k : E)) - α| ≤ η := by
    intro i j k hjk
    exact separated_correlation_bound hD f n A hA hg hhg (.inr (i, j)) (.inr (i, k))
      (selected_siblings_separated i hjk)
  have hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => (y g i j : E)) (fun g => (x g k : E)) - α| ≤ η := by
    intro i j k hki
    exact separated_correlation_bound hD f n A hA hg hhg (.inr (i, j)) (.inl k)
      (selected_child_parent_separated i j k hki)
  have hb : boundaryConstant L δ D ≤ η :=
    boundaryConstant_le_of_correlations A hA hD f L δ α η hL hδ hLip hDisp
      x y hrec hparent hchild hmixed
  exact exists_boundary_ge_of_le_max (fixedTransportSet hD)
    (fixedTransportSet_nonempty hD) A hb

end ThompsonNonamenability

end

end OAI
