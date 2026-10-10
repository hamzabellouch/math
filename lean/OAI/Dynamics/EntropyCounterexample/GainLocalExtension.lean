import OAI.Dynamics.EntropyCounterexample.ClockProfiles
import OAI.Dynamics.EntropyCounterexample.GainCircle
import OAI.Dynamics.EntropyCounterexample.C1CoordinatePullback

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem340

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def standardGain (L : ℝ) (x : StandardClock) : ℝ :=
  AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (clockHomeomorph.symm x)

lemma standardGain_continuous (L : ℝ) : Continuous (standardGain L) :=
  (gainProfile_liftIco_continuous L).comp clockHomeomorph.symm.continuous

lemma standardGain_param (L t : ℝ) :
    standardGain L (clockHomeomorph (t : AddCircle (100 : ℝ))) = periodicGain L t := by
  simp only [standardGain, clockHomeomorph.symm_apply_apply,
    gainProfile_liftIco_coe_eq_periodicGain]

lemma standardGain_mem_Icc {L : ℝ} (hL : 0 ≤ L) (x : StandardClock) :
    standardGain L x ∈ Set.Icc (0 : ℝ) L :=
  gainProfile_liftIco_mem_Icc hL _

theorem standardGain_hasLocalC1Extension (L : ℝ) :
    HasLocalC1Extension (fun x : StandardClock => x.1) (standardGain L) := by
  apply hasLocalC1Extension_of_clock_lift
  simpa only [standardGain_param] using (periodicGain_contDiff L).of_le
    (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)

theorem standardGain_hasLocalC1Extension_manifold (L : ℝ) (q : ℕ) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => standardGain L x.1) :=
  (standardGain_hasLocalC1Extension L).clock_coordinate

end Problem340

end

end OAI
