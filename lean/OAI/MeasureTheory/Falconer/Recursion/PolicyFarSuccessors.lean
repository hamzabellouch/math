import OAI.MeasureTheory.Falconer.Shells.PolicyPositiveBranches
import OAI.MeasureTheory.Falconer.Estimates.FarCellCount

namespace OAI

/-! # Actual positive states of a comparable far collision

The two new endpoint cells lie in the same original endpoint cell. Both
retain the descriptor masks and reset only the positive interval and index.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

private theorem partner_lengths (P : PolicyJetData m) (a : ℕ)
    (U : List (Fin (m+3) → Bool)) (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    row.1.length = a-P.a ∧ row.2.length = a-P.a := by
  have hp := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
  exact ⟨(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp.1).1,
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp.2).1⟩

def farPositiveSuccessor (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) : PolicyJetData m :=
  (P.onCells a ha (U++row.1) (U++row.2)
    (by rw [List.length_append,hU,(partner_lengths P a U row hr).1]; omega)
    (by rw [List.length_append,hU,(partner_lengths P a U row hr).2]; omega)).positiveSuccessor
      P.t P.base_right (P.i+1)

theorem farPositiveSuccessor_state (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    (P.farPositiveSuccessor a ha U hU row hr).positiveBranchState = .D a P.t (P.i+1) := rfl

theorem farPositiveSuccessor_count (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) (w₀ : Sphere (m+3)) :
    (P.farPositiveSuccessor a ha U hU row hr).positiveCount w₀ =
      (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
        P.N P.σ P.J (P.i+1) P.q a P.t (U++row.1) (U++row.2)).toReal := rfl

theorem farPositiveSuccessor_geometry (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    let S := P.farPositiveSuccessor a ha U hU row hr
    125*(((m+3:ℕ):ℝ)+1)*(S.Q.descendant S.X).side ≤
        ‖(S.Q.descendant S.X).center-(S.Q.descendant S.Y).center‖ ∧
      ‖(S.Q.descendant S.X).center-(S.Q.descendant S.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(S.Q.descendant S.X).side := by
  intro S
  have hgeom := (Finset.mem_filter.mp hr).2
  have hlen := (partner_lengths P a U row hr).1
  have hside : ((P.Q.descendant U).descendant row.1).side =
      (P.Q.descendant U).side/(2:ℝ)^(a-P.a) := by rw [DyadicCube.descendant_side,hlen]
  change 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant (U++row.1)).side ≤
      ‖(P.Q.descendant (U++row.1)).center-(P.Q.descendant (U++row.2)).center‖ ∧
    ‖(P.Q.descendant (U++row.1)).center-(P.Q.descendant (U++row.2)).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant (U++row.1)).side
  simp only [DyadicCube.descendant_append,hside]
  rw [norm_sub_rev]
  constructor
  · convert hgeom.1 using 1; ring
  · have hp : 0 < (P.Q.descendant U).side :=
      P.Q.descendant_side_pos (by rw [P.unit]; norm_num) U
    calc
      _ ≤ 1100*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant U).side/(2:ℝ)^(a-P.a) := hgeom.2
      _ = 1100*(((m+3:ℕ):ℝ)+1)*((P.Q.descendant U).side/(2:ℝ)^(a-P.a)) := by ring
      _ ≤ _ := by gcongr; norm_num


theorem farCollisionMaximum_le_positive_successors (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (w₀ : Sphere (m+3)) (M : ℝ)
    (hX : ∀ row, ∀ hr : row ∈ farCellPartners (P.Q.descendant P.X) P.ρ (a-P.a),
      (P.farPositiveSuccessor a ha P.X P.X_length row hr).positiveCount w₀ ≤ M)
    (hY : ∀ row, ∀ hr : row ∈ farCellPartners (P.Q.descendant P.Y) P.ρ (a-P.a),
      (P.farPositiveSuccessor a ha P.Y P.Y_length row hr).positiveCount w₀ ≤ M) :
    farCollisionMaximum w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
      P.N P.σ P.J (P.i+1) P.q a P.t P.X P.Y (a-P.a) ≤ ENNReal.ofReal M := by
  let := P.regular.probability
  unfold farCollisionMaximum
  apply Finset.sup_le
  intro z hz
  have hz' := Finset.mem_product.mp hz
  apply max_le
  · rw [← ENNReal.ofReal_toReal (positiveCollisionCount_ne_top w₀ P.Q P.ρ
      (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q a P.t
      (P.X++z.1.1) (P.X++z.1.2))]
    exact ENNReal.ofReal_le_ofReal (hX z.1 hz'.1)
  · rw [← ENNReal.ofReal_toReal (positiveCollisionCount_ne_top w₀ P.Q P.ρ
      (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q a P.t
      (P.Y++z.2.1) (P.Y++z.2.2))]
    exact ENNReal.ofReal_le_ofReal (hY z.2 hz'.2)

end PolicyJetData
end Falconer

end OAI
