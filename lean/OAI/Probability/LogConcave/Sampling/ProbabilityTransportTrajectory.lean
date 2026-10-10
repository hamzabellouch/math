import Mathlib
import OAI.Probability.LogConcave.Dynamics.FullProbabilityFlow
import OAI.Probability.LogConcave.Sampling.TerminalBackward

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_zero_trajectory (t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t z=
      fullProbabilityFlow hF x hr hl t z := by
  apply GlobalODE.flow_restrict
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
    (fullProbabilityVelocity_continuous hF x hr hl)
    (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (fun u _ => fullProbabilityVelocity_lipschitz hF x hr hl u)
    (Icc_subset_Icc_right hT1.le)
  intro u hu y
  rw [clampedProbabilityVelocity_eq F x r T hT0 hu,
    fullProbabilityVelocity_eq F x r hu.1 (hu.2.trans_lt hT1)]

lemma probabilityTransport_trajectory (s t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s t
      (fullProbabilityFlow hF x hr hl s z)=fullProbabilityFlow hF x hr hl t z := by
  rw [←probabilityTransport_zero_trajectory hF x hr hl hT0 hT1 s z,
    probabilityTransport_cocycle,probabilityTransport_zero_trajectory]

lemma terminalForward_trajectory (s : Icc (0:ℝ) T) (z : Point d) :
    terminalForward hF x hr hl hT0 hT1 (s,fullProbabilityFlow hF x hr hl s z)=
      fullProbabilityFlow hF x hr hl T z := by
  rw [terminalForward_eq]
  exact probabilityTransport_trajectory hF x hr hl hT0 hT1 s ⟨T,hT0,le_rfl⟩ z

lemma terminalBackward_trajectory (s : Icc (0:ℝ) T) (z : Point d) :
    terminalBackward hF x hr hl hT0 hT1 (s,fullProbabilityFlow hF x hr hl T z)=
      fullProbabilityFlow hF x hr hl s z := by
  rw [terminalBackward_eq]
  exact probabilityTransport_trajectory hF x hr hl hT0 hT1 ⟨T,hT0,le_rfl⟩ s z

end LogConcaveSampling

end

end

end

end OAI
