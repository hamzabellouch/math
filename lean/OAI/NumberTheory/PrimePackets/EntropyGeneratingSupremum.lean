import OAI.NumberTheory.PrimePackets.GeneratingObservationEntropy

namespace OAI

/-! # Computing metric entropy using generating finite observations -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace PrimeDegreePackets

variable {Y : Type*} [mY : MeasurableSpace Y]

theorem measureEntropy_eq_iSup_generating
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ)
    {k : ℕ → ℕ} (Q : ∀ n, Y → Fin (k n))
    (hQ : ∀ n b, MeasurableSet {y | Q n y = b})
    (hmono : Monotone (fun n => observationSigma (Q n)))
    (hgen : (⨆ n, observationSigma (Q n)) = mY) :
    measureEntropy μ T = ⨆ n, ENNReal.ofReal (observationEntropyRate μ T (Q n)) := by
  let E := ⨆ n, ENNReal.ofReal (observationEntropyRate μ T (Q n))
  apply le_antisymm
  · change measureEntropy μ T ≤ E
    by_cases hE : E = ∞
    · rw [hE]
      exact le_top
    apply iSup_le
    intro l
    apply iSup_le
    intro P
    apply iSup_le
    intro hP
    apply ENNReal.ofReal_le_of_le_toReal
    have hbound n : observationEntropyRate μ T P ≤
        E.toReal + conditionalObservationEntropy μ P (Q n) := by
      have hrate : observationEntropyRate μ T (Q n) ≤ E.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hE).mp (le_iSup (fun n =>
          ENNReal.ofReal (observationEntropyRate μ T (Q n))) n)
      exact (observationEntropyRate_le_add_conditional μ hT P (Q n) hP (hQ n)).trans
        (add_le_add hrate le_rfl)
    have hlim : Tendsto (fun n => E.toReal + conditionalObservationEntropy μ P (Q n))
        atTop (𝓝 (E.toReal + 0)) := tendsto_const_nhds.add
      (conditionalObservationEntropy_tendsto_zero μ P hP Q hQ hmono hgen)
    have H := ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
    simpa only [add_zero] using H
  · apply iSup_le
    intro n
    exact le_iSup_of_le (k n) (le_iSup_of_le (Q n) (le_iSup_of_le (hQ n) le_rfl))

end PrimeDegreePackets

end

end OAI
