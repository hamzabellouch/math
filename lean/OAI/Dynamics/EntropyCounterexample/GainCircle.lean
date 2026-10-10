import OAI.Dynamics.EntropyCounterexample.GainProfile

namespace OAI

noncomputable section

namespace Problem340

section CircleLift

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma gainProfile_liftIco_continuous (L : ℝ) :
    Continuous (AddCircle.liftIco (100 : ℝ) 0 (gainProfile L)) := by
  apply AddCircle.liftIco_zero_continuous
  · have h0 : gainProfile L 0 = 0 := gainProfile_zero_outside (by norm_num)
    have h100 : gainProfile L 100 = 0 := gainProfile_zero_outside (by norm_num)
    exact h0.trans h100.symm
  · exact (gainProfile_contDiff L).continuous.continuousOn

lemma gainProfile_liftIco_mem_Icc {L : ℝ} (hL : 0 ≤ L)
    (t : AddCircle (100 : ℝ)) :
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) t ∈ Set.Icc (0 : ℝ) L := by
  exact gainProfile_mem_Icc hL _

lemma gainProfile_liftIco_eq_gain (L : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (7 : ℝ) 90) :
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) = L := by
  rw [AddCircle.liftIco_zero_coe_apply (by constructor <;> linarith [ht.1, ht.2])]
  exact gainProfile_eq_gain L ht

lemma gainProfile_liftIco_eq_zero (L : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (2 : ℝ) 5) :
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) = 0 := by
  rw [AddCircle.liftIco_zero_coe_apply (by constructor <;> linarith [ht.1, ht.2])]
  exact gainProfile_eq_zero L ht

end CircleLift

end Problem340

end

end OAI
