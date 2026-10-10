import OAI.NumberTheory.TotientAsymptotic.WeightedMass

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- The weighted mass comparison includes every exceptional value and tuple. -/
theorem weighted_value_mass_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |normalizedCount (N k) x-M x H (fk k)/G x (m x)| ≤ δ H+ε := by
  obtain ⟨δv,hδv,hv⟩ := candidate_value_comparison hscale hstruct hbox hren hmertens h26 h51
  obtain ⟨δm,hδm,hm⟩ := candidate_mass_normalized hpnt hbox hren hmertens k hk
  refine ⟨fun H => δv H+δm H,by simpa using hδv.add hδm,?_⟩
  filter_upwards [hv,hm] with H hv hm
  intro ε hε
  filter_upwards [hv (ε/2) (by positivity),hm (ε/2) (by positivity),scale_eventually_pos]
    with x hv hm hN
  change 0 < tupleNormalization x at hN
  have he : |normalizedCount (N k) x-((candidateTuples x H k).card : ℝ)/tupleNormalization x| ≤ δv H+ε/2 := by
    change |N k x/tupleNormalization x-_| ≤ _
    rw [← sub_div,abs_div,abs_of_pos hN,abs_sub_comm]
    exact (div_le_iff₀ hN).mpr (hv k)
  exact (abs_sub_le _ _ _).trans ((add_le_add he hm).trans_eq (by ring))

theorem weighted_value_coefficient_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |normalizedCount (N k) x-AH H (fk k) (theta x)| ≤ δ H+ε := by
  obtain ⟨δv,hδv,hv⟩ := weighted_value_mass_approximation hscale hstruct hpnt hbox hren hmertens h26 h51 k hk
  obtain ⟨δm,hδm,hm⟩ := mass_finite_coefficient_approximation hbox hmertens hren hconc
  refine ⟨fun H => δv H+δm H,by simpa using hδv.add hδm,?_⟩
  let f : ℝ → ℝ := fun r => fk k (max r 0)
  have hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1 := fun r =>
    ⟨fk_nonneg k (le_max_right _ _),fk_le_one k (le_max_right _ _)⟩
  have hsame (d : ℕ) : f ((ell d : ℝ)/d)=fk k ((ell d : ℝ)/d) := by
    dsimp [f]
    rw [max_eq_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hmass (x : ℝ) (H : ℕ) : M x H f=M x H (fk k) := by
    simp only [mass_eq_prefix_denominators,hsame]
  have hcoeff (H : ℕ) (s : ℝ) : AH H f s=AH H (fk k) s := by
    unfold AH
    simp only [hsame]
  filter_upwards [hv,hm] with H hv hm
  intro ε hε
  filter_upwards [hv (ε/2) (by positivity),hm f hf (ε/2) (by positivity)] with x hv hm
  rw [hmass,hcoeff] at hm
  exact (abs_sub_le _ _ _).trans ((add_le_add hv hm).trans_eq (by ring))

/-- The additive weighted asymptotic and its uniform arithmetic coefficient. -/
theorem conditional_companion_additive (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (k : ℕ) (hk : 1 ≤ k) :
    TendstoUniformlyOn (fun H => AH H (fk k)) (A (fk k)) atTop (Set.Ico (0 : ℝ) 1) ∧
      Tendsto (fun x => normalizedCount (N k) x-A (fk k) (theta x)) atTop (nhds 0) := by
  obtain ⟨δ,hδ,happ⟩ := weighted_value_coefficient_approximation hscale hstruct hpnt
    hbox hren hmertens h26 h51 hconc k hk
  apply coefficient_convergence_from_phase_comparison
  intro ε hε
  have he : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      |normalizedCount (N k) x-AH H (fk k) (theta x)| ≤ ε := by
    filter_upwards [happ,hδ.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity))]
      with H hH hδH
    filter_upwards [hH (ε/2) (by positivity)] with x hx
    exact hx.trans (by linarith)
  exact eventually_atTop.mp he

end TotientAsymptotic

end

end OAI
