import OAI.Combinatorics.BalancedRyser.Selection.SelectionFinalLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryMarginal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V] [Nonempty V]

theorem finalLaw_weight_eq_path_integral (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (a : I → V) :
    (finalLaw p q G hno).weight a =
      ∫ ω, (sourceTerminalOutcomeLaw p q G hno
        (ω (p.lastMainTime q (Fintype.card I))).1).weight a
          ∂snapshotPathLaw p q G := by
  exact (integral_stateObservable_eq_historyWeight p q G _
    (fun out => (sourceTerminalOutcomeLaw p q G hno out).weight a)).symm

theorem successMass_finalLaw_eq_path_probability (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    successMass (finalLaw p q G hno) =
      (snapshotPathLaw p q G).real {ω | ∃ S,
        (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧ SourceTailCheck p q G S} := by
  rw [successMass_finalLaw]
  change _ = (snapshotPathLaw p q G).real {ω |
    (ω (p.lastMainTime q (Fintype.card I))).1 ∈
      {out | ∃ S, out = some S ∧ SourceTailCheck p q G S}}
  rw [state_event_real_eq_historyWeight, Fintype.sum_option]
  simp [mainStageWeight]

theorem cylinderMass_finalLaw_eq_path_integral (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (finalLaw p q G hno) J prescribed =
      ∫ ω, cylinderMass (sourceTerminalOutcomeLaw p q G hno
        (ω (p.lastMainTime q (Fintype.card I))).1) J prescribed
          ∂snapshotPathLaw p q G := by
  rw [cylinderMass_finalLaw]
  exact (integral_stateObservable_eq_historyWeight p q G _
    (fun out => cylinderMass (sourceTerminalOutcomeLaw p q G hno out) J prescribed)).symm

theorem occupancyFailureMass_finalLaw_eq_path_integral (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) :
    occupancyFailureMass (finalLaw p q G hno) A line T ρ =
      ∫ ω, occupancyFailureMass (sourceTerminalOutcomeLaw p q G hno
        (ω (p.lastMainTime q (Fintype.card I))).1) A line T ρ
          ∂snapshotPathLaw p q G := by
  rw [occupancyFailureMass_finalLaw]
  exact (integral_stateObservable_eq_historyWeight p q G _
    (fun out => occupancyFailureMass (sourceTerminalOutcomeLaw p q G hno out) A line T ρ)).symm

end Balanced.Selection.Process

end

end OAI
