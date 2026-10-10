import Mathlib
import OAI.Computability.VertexCover.Reduction.PrivateProjectionSurvival
import OAI.Computability.VertexCover.Reduction.BatchesTripleSum

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                              

namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem weightGroup_residual_budget (Φ : LabelCover) {d : ℕ}
    (Q : (Φ.restrictionForm d).Projection)
    (hQ : ∀ k f, Φ.weightProjection k (Q f) = Q (Φ.weightProjection k f))
    (f : Φ.RestrictionSpace d) :
    (∑ j : Fin d, (Φ.restrictionForm d).energy (Q.residual (Φ.weightGroup j f))) ≤
      (Φ.restrictionForm d).energy (Q.residual f) :=
  finDifference_residual_budget _ Φ.weightProjection_commute Q hQ f

theorem weightGroup_pair_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, ∑ k : Fin d,
      ((Φ.restrictionForm d).energy ((Φ.weightProjection k).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA))) +
       (Φ.restrictionForm d).energy ((Φ.starProjection k).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA))))) ≤ 8*d := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ k : Fin d,
        ((Φ.restrictionForm d).energy ((Φ.weightProjection k).residual
          (Φ.restrictionFunction A hA)) +
         (Φ.restrictionForm d).energy ((Φ.starProjection k).residual
          (Φ.restrictionFunction A hA))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_add_distrib]
      apply add_le_add
      · exact Φ.weightGroup_residual_budget (Φ.weightProjection k)
          (fun i f => Φ.weightProjection_commute i k f) _
      · exact Φ.weightGroup_residual_budget (Φ.starProjection k)
          (fun i f => (Φ.condition_weightProjection_commute (Φ.starKey k) i f).symm) _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      have hw := Φ.restriction_weight_budget A hA
      have hs := Φ.restriction_star_budget A hA
      linarith

theorem weightGroup_seed_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, ∑ e : PositionPair d,
      (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA)))) ≤ 8*(d:ℝ)^2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ e : PositionPair d, (Φ.restrictionForm d).energy
        ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA)) := by
      apply Finset.sum_le_sum
      intro e _
      exact Φ.weightGroup_residual_budget (Φ.seedProjection e)
        (fun i f => (Φ.condition_weightProjection_commute
          (fun seed : Φ.Seeds d => Function.update seed e ⟨0, Φ.M_pos⟩) i f).symm) _
    _ ≤ _ := Φ.restriction_seed_budget A hA

theorem privateProjection_batch_bound (Φ : LabelCover) {d h : ℕ} (hh : 3 ≤ h)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    ((d-1).choose (h-1) : ℝ) * (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) ≤
      (∑ J ∈ batches d h, ∑ j ∈ J, (Φ.restrictionForm d).energy
        (Φ.privateProjection J j (Φ.restrictionFunction A hA))) +
      ((d-2).choose (h-2) : ℝ)*(8*d) + ((d-3).choose (h-3) : ℝ)*(8*(d:ℝ)^2) := by
  classical
  let B := Φ.restrictionForm d
  let f := Φ.restrictionFunction A hA
  let pairLoss := fun j k : Fin d => B.energy ((Φ.weightProjection k).residual (Φ.weightGroup j f)) +
    B.energy ((Φ.starProjection k).residual (Φ.weightGroup j f))
  let seedLoss := fun (j : Fin d) (e : PositionPair d) =>
    B.energy ((Φ.seedProjection e).residual (Φ.weightGroup j f))
  have hsurv : (∑ J ∈ batches d h, ∑ j ∈ J, B.energy (Φ.weightGroup j f)) ≤
      (∑ J ∈ batches d h, ∑ j ∈ J, B.energy (Φ.privateProjection J j f)) +
      (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, pairLoss j k) +
      (∑ J ∈ batches d h, ∑ j ∈ J,
        ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)), seedLoss j e) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro J _
    apply Finset.sum_le_sum
    intro j _
    exact Φ.privateProjection_survival J j f
  have hpair := batches_pair_sum_le (by omega : 2 ≤ h) pairLoss
    (fun j k => add_nonneg (B.energy_nonneg _) (B.energy_nonneg _))
  have htriple := batches_triple_sum_le hh
    (fun e : PositionPair d => e.1.1) (fun e : PositionPair d => e.1.2)
    (fun e => ne_of_lt e.2) seedLoss (fun _ _ => B.energy_nonneg _)
  have hsets (J : Finset (Fin d)) (j : Fin d) :
      (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)) =
        Finset.univ.filter (fun e : PositionPair d =>
          e.1.1 ∈ J ∧ e.1.2 ∈ J ∧ ¬ (e.1.1 = j ∨ e.1.2 = j)) := by
    ext e
    simp only [internalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [hsets] at hsurv
  rw [batches_singleton_sum (by omega : 1 ≤ h), Φ.weightGroup_energy_sum A hA] at hsurv
  have hpb : (∑ j, ∑ k, pairLoss j k) ≤ 8*d := Φ.weightGroup_pair_budget A hA
  have hsb : (∑ j, ∑ e, seedLoss j e) ≤ 8*(d:ℝ)^2 := Φ.weightGroup_seed_budget A hA
  have hpb' := mul_le_mul_of_nonneg_left hpb (Nat.cast_nonneg ((d-2).choose (h-2)) : (0:ℝ) ≤ _)
  have hsb' := mul_le_mul_of_nonneg_left hsb (Nat.cast_nonneg ((d-3).choose (h-3)) : (0:ℝ) ≤ _)
  dsimp only [B, f] at hsurv
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
