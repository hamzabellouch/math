import OAI.Probability.SATComputability.CompiledTrials
import OAI.Probability.SATComputability.PressureSigns

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped NNReal

local instance trialCompletenessRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem trialDensityNN_of_pos {t : TrialData} (ht : 0 < t.1) :
    (trialDensityNN t : ℝ) = (t.1 : ℝ) := by
  change ((max 0 t.1 : ℚ) : ℝ) = (t.1 : ℝ)
  rw [max_eq_right ht.le]

theorem functional_list_encoding (a : ℝ≥0) (β : ℝ) {r : ℕ}
    (ms : List ℚ) (hlen : ms.length = r) (t : RationalTree (r+1)) (m : Fin r → ℚ)
    (hget : ∀ i, ms.get i = m (Fin.cast hlen i)) :
    functional (satModel a β) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) (encodeTree (r+1) t)))
      (fun i => (ms.get i : ℝ)) =
      functional (satModel a β) r (rationalTreeValue (r+1) t) (fun i => (m i : ℝ)) := by
  subst r
  rw [decodeTree_encodeTree]
  congr 1
  funext i
  exact congrArg (fun q : ℚ => (q : ℝ)) (hget i)

theorem satTrialEvaluation_sound {j : ℕ} (hj : satTrialEvaluation.valid j = true)
    (hneg : satTrialEvaluation.value j < 0) :
    limitingCenter 3 ≤ (satTrialEvaluation.density j : ℝ) := by
  by_contra h
  have hv := satTrialEvaluation_valid hj
  have ha : (0 : ℝ≥0) < trialDensityNN (decodeTrial j) := by
    change (0 : ℝ) < (trialDensityNN (decodeTrial j) : ℝ)
    rw [trialDensityNN_of_pos hv.1]
    exact_mod_cast hv.1
  have hb : (0 : ℝ) < ((decodeTrial j).2.1 : ℝ) := by exact_mod_cast hv.2.1
  have hbelow : (trialDensityNN (decodeTrial j) : ℝ) < limitingCenter 3 := by
    rw [trialDensityNN_of_pos hv.1]
    exact lt_of_not_ge h
  have hp := satPressure_subcritical ha hbelow hb
  exact (not_lt_of_ge (hp.trans (satTrialEvaluation_bound hj))) hneg

theorem satTrialEvaluation_dense (a : ℚ) (ha : 0 < a) (b : ℕ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ j, satTrialEvaluation.valid j = true ∧ satTrialEvaluation.density j = a ∧
      (decodeTrial j).2.1 = b ∧
      satTrialEvaluation.value j < satPressure ⟨(a : ℝ), by exact_mod_cast ha.le⟩ b + ε := by
  let aNN : ℝ≥0 := ⟨a, by exact_mod_cast ha.le⟩
  have haNN : 0 < aNN := by
    change (0 : ℝ) < (a : ℝ)
    exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨r,t,m,hm,hval⟩ := exists_fully_rational_trial_near_pressure haNN hbR hε
  let ms := List.ofFn m
  let code := encodeTree (r+1) t
  let data : TrialData := (a,b,code,ms)
  have hlen : ms.length = r := List.length_ofFn
  have hget (i : Fin ms.length) : ms.get i = m (Fin.cast hlen i) := List.get_ofFn _ _
  have hm' : Exponents (fun i : Fin ms.length => (ms.get i : ℝ)) := by
    constructor
    · intro i j hij
      simpa only [hget] using hm.1 (show Fin.cast hlen i < Fin.cast hlen j from hij)
    · intro i
      simpa only [hget] using hm.2 (Fin.cast hlen i)
  have he : exponentCheck ms = true := (exponentCheck_iff ms).mpr hm'
  have hd : trialDataValid data = true := (trialDataValid_iff data).mpr ⟨ha,hb,he⟩
  have hrate : trialDensityNN data = aNN := by
    apply Subtype.ext
    simp only [trialDensityNN, data, aNN, max_eq_right ha.le]
  refine ⟨Encodable.encode data, ?_, ?_, ?_, ?_⟩
  · simpa only [satTrialEvaluation, decodeTrial_encode] using hd
  · simp only [satTrialEvaluation, decodeTrial_encode, data]
  · simp only [decodeTrial_encode, data]
  · change trialValue (decodeTrial (Encodable.encode data)) < _
    rw [decodeTrial_encode, trialValue_eq_functional data he, hrate]
    change functional (satModel aNN (b : ℝ)) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) (encodeTree (r+1) t)))
      (fun i => (ms.get i : ℝ)) < _
    rw [functional_list_encoding aNN b ms hlen t m hget]
    exact hval

theorem satTrialEvaluation_negative_witness (a : ℚ) (ha : 0 < a) (b : ℕ) (hb : 0 < b)
    (hneg : satPressure ⟨(a : ℝ), by exact_mod_cast ha.le⟩ b < 0) :
    ∃ j, satTrialEvaluation.valid j = true ∧ satTrialEvaluation.density j = a ∧
      satTrialEvaluation.value j < 0 := by
  obtain ⟨j,hj,hd,_,hv⟩ := satTrialEvaluation_dense a ha b hb _ (neg_pos.mpr hneg)
  exact ⟨j,hj,hd,by simpa only [add_neg_cancel] using hv⟩

end FixedClauseThreshold.Computability

end OAI
