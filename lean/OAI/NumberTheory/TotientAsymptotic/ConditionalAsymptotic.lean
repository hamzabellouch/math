import OAI.NumberTheory.TotientAsymptotic.ValueComparison

namespace OAI

/-! The unweighted asymptotic, conditional only on the precisely cited
published inputs. All tuple, collision, mass and coverage estimates are proved. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The main asymptotic and its finite arithmetic coefficient. -/
theorem conditional_totient_asymptotic_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput) :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0<cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) := by
  obtain ⟨δ,hδ,happ⟩ := value_finite_coefficient_approximation hscale hstruct hpnt hbox hren hmertens h26 h51 hconc
    (a := 1) (by norm_num)
  apply coefficient_conclusions_of_internal_comparison hscale
  intro ε hε
  have he : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      |normalizedCount V x-AH H (fun _ => 1) (theta x)| ≤ ε := by
    filter_upwards [happ,hδ.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity))]
      with H hH hδH
    filter_upwards [hH (ε/2) (by positivity),eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hh := hx x (by simp) le_rfl
    rw [div_self (ne_of_gt (zero_lt_one.trans hx1)),one_mul] at hh
    exact hh.trans (by linarith)
  exact eventually_atTop.mp he


/-- The original published-input interface remains available. -/
theorem conditional_totient_asymptotic (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput) :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0<cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) :=
  conditional_totient_asymptotic_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc

end TotientAsymptotic

end

end OAI
