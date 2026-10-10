import OAI.NumberTheory.TotientAsymptotic.ConditionalAsymptotic
import OAI.NumberTheory.TotientAsymptotic.ValueMass

namespace OAI

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Fixed-scale regular variation, proved using the same arithmetic mass at
both endpoints. No continuity of the phase coefficient is required. -/
theorem conditional_totient_scaling_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => V (c*x)/V x) atTop (nhds c) := by
  by_cases hc1 : 1 ≤ c
  · exact scaling_of_internal_comparison hc hscale
      (common_endpoint_comparison hscale hstruct hpnt hbox hren hmertens h26 h51 hc1)
  · have hi : 1 ≤ 1/c := (one_le_div hc).mpr (le_of_not_ge hc1)
    have ht := inverse_scaling_of_internal_comparison (one_div_pos.mpr hc) hscale
      (common_endpoint_comparison hscale hstruct hpnt hbox hren hmertens h26 h51 hi)
    simpa [div_div, mul_comm] using ht

/-- The complete main theorem of the supplied manuscript, conditional only on
its precisely cited published inputs. -/
theorem conditional_main_theorem_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput) :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => V (c*x)/V x) atTop (nhds c) := by
  obtain ⟨hu,hb,ha⟩ := conditional_totient_asymptotic_of_structure hscale hstruct hpnt hbox hren hmertens h26 h51 hconc
  exact ⟨hu,hb,ha,fun _ hc => conditional_totient_scaling_of_structure hscale hstruct hpnt hbox hren hmertens h26 h51 hc⟩


/-- The original published-input interface remains available. -/
theorem conditional_totient_scaling (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => V (c*x)/V x) atTop (nhds c) :=
  conditional_totient_scaling_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hc

theorem conditional_main_theorem (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput) :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => V (c*x)/V x) atTop (nhds c) :=
  conditional_main_theorem_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc

end TotientAsymptotic

end

end OAI
