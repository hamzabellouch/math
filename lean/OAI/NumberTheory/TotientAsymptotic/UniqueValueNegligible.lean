import OAI.NumberTheory.TotientAsymptotic.CandidateComparison

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma nonunique_values_negligible (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop,
        ((nonuniqueValues x H).card : ℝ) ≤ (δ H+ε)*tupleNormalization x := by
  obtain ⟨δe,hδe,he⟩ := basic_exception_values_negligible hscale hstruct hbox hren hmertens
  obtain ⟨δd,hδd,hd⟩ := bad_tuple_discard hbox hren hmertens h26
  obtain ⟨δc,hδc,hc⟩ := good_collision_count h51 hmertens hbox hren
  refine ⟨fun H => |δe H|+|δd H|+|δc H|,by simpa using (hδe.abs.add hδd.abs).add hδc.abs,?_⟩
  filter_upwards [he,hd,hc,unique_prefix_finite_comparison] with H he hd hc hf
  intro ε hε
  filter_upwards [he ε hε,hd,hc,hf,scale_eventually_pos] with x he hd hc hf hN
  have he' : ((basicExceptionValues x H).card : ℝ)≤(|δe H|+ε)*tupleNormalization x :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (δe H)]) hN.le)
  have hd' : ((badTupleFinset x H x).card : ℝ)≤|δd H| *tupleNormalization x :=
    (hd x le_rfl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hc' : ((goodCollisionPairs x H x).card : ℝ)≤|δc H| *tupleNormalization x :=
    (hc x le_rfl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hc0 : (0 : ℝ)≤(goodCollisionPairs x H x).card := Nat.cast_nonneg _
  nlinarith [hf.1]

end TotientAsymptotic

end

end OAI
