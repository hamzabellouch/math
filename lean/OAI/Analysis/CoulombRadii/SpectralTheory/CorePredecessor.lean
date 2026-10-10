import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.CoreBudget
import OAI.Analysis.CoulombRadii.Screening.CoreMoment

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem atomic_predecessor_from_physical_mean : ∃ C : ℝ, 0≤C ∧
    ∀ (Z : ℕ) (hZ : 1≤Z) {n : ℕ} (u : H1Vector n),
    Antisymmetric u → mass u=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom (atom Z hZ) → form (atom Z hZ) u≤E →
    ∀ {t : ℝ}, 0<t → expectedPopulation u (Metric.ball 0 (2*t))≤(Z:ℝ)-1 →
    (sectorFormBottom (atom Z hZ) (Z-1)).toReal≤
      E+NeutralAtom.fixedCoreMomentBound t*C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  obtain ⟨C,hC,HC⟩ := RecordedEnsemble.atomic_zero_offset_core_deletion
  refine ⟨C,hC,?_⟩
  intro Z hZ n u ha hm E hE he t ht hmean
  obtain ⟨T,hT,hF,hS,hO,hM,hform⟩ := HC (atom Z hZ) (fun _ => rfl) u ha hm hE he ht
  have hs : T.CoreSupported (Metric.ball 0 (2*t)) := by
    simpa only [Metric.ball,dist_zero_right] using hS
  have hm' : 1≤(Z:ℝ)-T.coreMean := by
    have hp := RecordedEnsemble.coreMean_le_population hT measurableSet_ball hs
    linarith
  have hsecond := RecordedEnsemble.zero_offset_core_deficit_moment Z hZ u ha hm hE he ht T hT hO
  let P := (sectorFormBottom (atom Z hZ) (Z-1)).toReal
  have hP : (P:EReal)=sectorFormBottom (atom Z hZ) (Z-1) := atom_sectorFormBottom_real Z hZ _
  have hEP : E≤P := EReal.coe_le_coe_iff.mp (hE.trans (by
    rw [hP]
    exact iInf_le (fun k => sectorFormBottom (atom Z hZ) k) (Z-1)))
  have H := T.predecessor_bound_of_core_budget (atom Z hZ) hF
    (atom_sectorFormBottom_antitone Z hZ) hE hP.le hEP
    (NeutralAtom.fixedCoreMomentBound_pos t) hM hm' hsecond hform
  simpa only [mul_assoc] using H

end Coulomb
end

end

end OAI
