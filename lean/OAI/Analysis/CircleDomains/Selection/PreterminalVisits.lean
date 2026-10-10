import OAI.Analysis.CircleDomains.Selection.VisitCardinality
import OAI.Analysis.CircleDomains.Topology.PathEndpoints

namespace OAI

/-! Visit multiplicities with the terminal parameter omitted. The extended
subtraction formula is justified by an exact all-time sum decomposition. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def terminalVisitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  if γ ⊤ = x then 1 else 0

def preterminalVisitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  visitCount γ x - terminalVisitCount γ x

theorem preterminalVisitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    preterminalVisitCount γ x =
      ∑' t : PathTime, if t ≠ ⊤ ∧ γ t = x then (1 : ℝ≥0∞) else 0 := by
  rw [preterminalVisitCount, visitCount_eq_tsum, ENNReal.tsum_eq_add_tsum_ite ⊤]
  have hfinite : terminalVisitCount γ x ≠ ∞ := by
    unfold terminalVisitCount
    split <;> simp
  change terminalVisitCount γ x + _ - terminalVisitCount γ x = _
  rw [ENNReal.add_sub_cancel_left hfinite]
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]

theorem visitCount_eq_preterminal_add_terminal (γ : C(PathTime, X)) (x : X) :
    visitCount γ x = preterminalVisitCount γ x + terminalVisitCount γ x := by
  rw [visitCount_eq_tsum, ENNReal.tsum_eq_add_tsum_ite ⊤,
    preterminalVisitCount_eq_tsum, add_comm]
  congr 1
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]

theorem preterminalVisitCount_target (γ : C(PathTime, X)) {b : X} (hb : FirstArrival b γ) :
    preterminalVisitCount γ b = 0 := by
  rw [preterminalVisitCount_eq_tsum]
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  have ht : ¬ (t ≠ ⊤ ∧ γ t = b) := by
    rintro ⟨ht, he⟩
    exact hb.2 t (lt_top_iff_ne_top.mpr ht) he
  simp only [ht, ite_false]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_terminalVisitCount :
    Measurable (fun q : C(PathTime, X) × X => terminalVisitCount q.1 q.2) := by
  unfold terminalVisitCount
  exact measurable_const.ite
    ((isClosed_eq ((continuous_eval_const ⊤).comp continuous_fst) continuous_snd).measurableSet)
    measurable_const

theorem measurable_preterminalVisitCount :
    Measurable (fun q : C(PathTime, X) × X => preterminalVisitCount q.1 q.2) :=
  measurable_visitCount.sub measurable_terminalVisitCount


end CircleDomainRigidity

end

end OAI
