import OAI.NumberTheory.TotientAsymptotic.LeastPrefix
import OAI.NumberTheory.TotientAsymptotic.ValueLower

namespace OAI

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The same negligible error controls every least-preimage interval; it counts
all exceptional values and all tuples above them. -/
theorem candidate_value_comparison (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ k : ℕ,
        |((candidateTuples x H k).card : ℝ)-N k x| ≤ (δ H+ε)*tupleNormalization x := by
  obtain ⟨δe,hδe,he⟩ := basic_exception_values_negligible hscale hstruct hbox hren hmertens
  obtain ⟨δd,hδd,hd⟩ := bad_tuple_discard hbox hren hmertens h26
  obtain ⟨δc,hδc,hc⟩ := good_collision_count h51 hmertens hbox hren
  refine ⟨fun H => 2*|δe H|+3*|δd H|+2*|δc H|,?_,?_⟩
  · simpa only [abs_zero,mul_zero,add_zero] using ((hδe.abs.const_mul 2).add
      (hδd.abs.const_mul 3)).add (hδc.abs.const_mul 2)
  filter_upwards [he,hd,hc,candidate_count_comparison,unique_prefix_finite_comparison]
    with H he hd hc hcompare hfinite
  intro ε hε
  filter_upwards [he (ε/2) (by positivity),hd,hc,hcompare,hfinite,scale_eventually_pos]
    with x he hd hc hcompare hfinite hN
  intro k
  have hd := hd x le_rfl
  have hc := hc x le_rfl
  have hEc : ((basicExceptionValues x H).card : ℝ) ≤ (|δe H|+ε/2)*tupleNormalization x :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (δe H)]) hN.le)
  have hDc : ((badTupleFinset x H x).card : ℝ) ≤ |δd H| *tupleNormalization x :=
    hd.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hCc : ((goodCollisionPairs x H x).card : ℝ) ≤ |δc H| *tupleNormalization x :=
    hc.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hh := hcompare k
  have hC0 : (0 : ℝ) ≤ (goodCollisionPairs x H x).card := Nat.cast_nonneg _
  nlinarith [hfinite.1,hfinite.2.1]

end TotientAsymptotic

end

end OAI
