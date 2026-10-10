import OAI.NumberTheory.TotientAsymptotic.ValueCoverage
import OAI.NumberTheory.TotientAsymptotic.ValueLower

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

theorem value_tuple_comparison (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        |((tupleFinset x H t).card : ℝ)-V t| ≤ (δ H+ε)*tupleNormalization x := by
  obtain ⟨δ₁,hd₁,h₁⟩ := tuple_excess_negligible hbox hren hmertens h26 h51
  obtain ⟨δ₂,hd₂,h₂⟩ := uncovered_values_negligible hscale hstruct hbox hren hmertens
  refine ⟨fun H => |δ₁ H|+|δ₂ H|,by simpa using hd₁.abs.add hd₂.abs,?_⟩
  filter_upwards [h₁,h₂,tuple_value_comparison] with H h1 h2 hc
  intro ε hε
  filter_upwards [h1,h2 ε hε,hc,scale_eventually_pos] with x h1 h2 hc hN
  intro t ht
  have ha : δ₁ H ≤ |δ₁ H|+|δ₂ H|+ε := by linarith [le_abs_self (δ₁ H),abs_nonneg (δ₂ H)]
  have hb : δ₂ H+ε ≤ |δ₁ H|+|δ₂ H|+ε := by linarith [le_abs_self (δ₂ H),abs_nonneg (δ₁ H)]
  apply abs_le.mpr
  constructor
  · have hh := (h2 t ht).trans (mul_le_mul_of_nonneg_right hb hN.le)
    linarith [(hc t).1]
  · exact (h1 t ht).trans (mul_le_mul_of_nonneg_right ha hN.le)

/-- The complete downstream comparison between actual distinct values and
finite arithmetic coefficients, uniformly over comparable endpoints. -/
theorem value_finite_coefficient_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    {a : ℝ} (ha : 0<a) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop,
      ∀ t : ℝ, a*x ≤ t → t ≤ x →
        |V t/tupleNormalization x-(t/x)*AH H (fun _ => 1) (theta x)| ≤ δ H+ε := by
  obtain ⟨δ₁,hd₁,h₁⟩ := value_tuple_comparison hscale hstruct hbox hren hmertens h26 h51
  obtain ⟨δ₂,hd₂,h₂⟩ := tuple_finite_coefficient_approximation hpnt hbox hmertens hren hconc ha
  refine ⟨fun H => δ₁ H+δ₂ H,by simpa using hd₁.add hd₂,?_⟩
  filter_upwards [h₁,h₂] with H h1 h2
  intro ε hε
  filter_upwards [h1 (ε/2) (by positivity),h2 (fun _ => 1) (fun _ => ⟨zero_le_one,le_rfl⟩)
    (ε/2) (by positivity),scale_eventually_pos] with x hv ht hN
  intro t hat htx
  change 0 < tupleNormalization x at hN
  have hc : |V t/tupleNormalization x-((tupleFinset x H t).card : ℝ)/tupleNormalization x| ≤ δ₁ H+ε/2 := by
    rw [← sub_div,abs_div,abs_of_pos hN,abs_sub_comm]
    exact (div_le_iff₀ hN).mpr (hv t htx)
  have hp := ht t hat htx
  rw [weightedTupleCount_one] at hp
  exact (abs_sub_le _ _ _).trans ((add_le_add hc hp).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
