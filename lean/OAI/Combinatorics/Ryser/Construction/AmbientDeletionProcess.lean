import OAI.Combinatorics.Ryser.Construction.AmbientDeletionTrials
import OAI.Combinatorics.Ryser.Construction.AmbientDeletionNumerics

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) : ℝ :=
  ∏ t : Fin (ambientTrialCount σ K),
    (1 - ambientPointRate σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a)

theorem ambientTrials_uniformSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (fun ω => x ∈ LineCover.survivors ∅ ω) = ambientSurvival σ u v huv a K := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (ambientTrials σ u v huv a ha K)
    (fun _ A => x ∉ LineCover.deleted ∅ A)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [ambientTrials, ambientTrialLaw_point_probability, ambientSurvival]

theorem ambientSurvival_lower (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    ambientDeletionDelta (Fintype.card k) K ≤ ambientSurvival σ u v huv a K := by
  apply ambientDeletionDelta_le_prod (Fintype.card k) K (Fintype.card F) hs
    Fintype.card_pos hsmall ?_ _ ?_
  · simpa only [Fintype.card_fin] using ambientTrialCount_mul_sub_one_le σ K
  · intro t
    exact ambientPointRate_le σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha

def ambientDeletionProcess (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    LineCover.DeletionProcess F (ambientDeletionConstant (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K) where
  shapes := ambientShapes F
  shapeCount := ambientShapes_count_le (ambientDeletionConstant_two_le _ _)
  shapeSize := ambientShapes_size_le (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  sparse := ambientShapes_sparse (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  trialsCount := ambientTrialCount σ K
  trials := ambientTrials σ u v huv a ha K
  trialsCount_le := ambientTrialCount_le σ K hs
  pointCap := by
    intro t x
    rw [ambientTrials, ambientTrialLaw_point_probability]
    apply (ambientPointRate_le σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lines_le (Fintype.card k) K
  survival := ambientSurvival σ u v huv a K
  survivalLower := ambientSurvival_lower σ u v huv a ha K hs hsmall
  uniformSurvival := ambientTrials_uniformSurvival σ u v huv a ha K
  lineCap := by
    intro l
    apply (ambientTrials_line_probability_sum_le σ u v huv a ha K l).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lineRate_le (Fintype.card k) K

end RyserCoveringCounterexample.Construction

end

end OAI
