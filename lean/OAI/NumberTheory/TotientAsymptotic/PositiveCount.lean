import OAI.NumberTheory.TotientAsymptotic.PositiveTupleWeight
import OAI.NumberTheory.TotientAsymptotic.WeightedCoefficient

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma companion_positive_bound (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input)
    {d k : ℕ} (hk : 1≤k) (hd : IsTotient d) (hseed : k*d<ell d)
    (hppt : PPTBoundedFiberPropagation d) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop, c≤normalizedCount (N k) x := by
  obtain ⟨c,hc,hpositive⟩ := positive_weighted_tuple_count hscale hstruct hbox hren hmertens h26 h51 hd hseed hppt
  obtain ⟨δ,hδ,hvalue⟩ := weighted_value_mass_approximation hscale hstruct hpnt hbox hren hmertens h26 h51 k hk
  obtain ⟨H,hpos,hval,htuple,hδH⟩ := (hpositive.and (hvalue.and
    ((tuple_mass_normalized_approximation hpnt hbox hren hmertens (a := 1) (by norm_num)).and
      (hδ.eventually (eventually_lt_nhds (show (0 : ℝ)<c/8 by positivity)))))).exists
  let f : ℝ → ℝ := fun r => fk k (max r 0)
  have hf : ∀ r, 0≤f r ∧ f r≤1 := fun r =>
    ⟨fk_nonneg k (le_max_right _ _),fk_le_one k (le_max_right _ _)⟩
  have hsame (d : ℕ) : f ((ell d : ℝ)/d)=fk k ((ell d : ℝ)/d) := by
    dsimp [f]
    rw [max_eq_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hm (x : ℝ) : M x H f=M x H (fk k) := by simp only [mass_eq_prefix_denominators,hsame]
  have ht (x : ℝ) : weightedTupleCount x H x f=weightedTupleCount x H x (fk k) := by
    simp only [weightedTupleCount,hsame]
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hpos,hval (c/8) (by positivity),htuple (c/4) (by positivity),
    scale_eventually_pos,eventually_gt_atTop (1 : ℝ)] with x hp hv htup hN hx
  change 0<tupleNormalization x at hN
  have htup := htup x (by simp) le_rfl f hf
  rw [hm,ht,div_self (zero_lt_one.trans hx).ne',one_mul] at htup
  have hp' : c≤weightedTupleCount x H x (fk k)/tupleNormalization x := (le_div_iff₀ hN).mpr hp
  have h₁ := (abs_le.mp htup).2
  have h₂ := (abs_le.mp hv).1
  linarith

end TotientAsymptotic

end

end OAI
