import OAI.NumberTheory.TotientAsymptotic.TupleTotients
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The actual count can exceed the number of represented values only by
the discarded tuples and the collision error, both already proved small. -/
theorem tuple_excess_negligible (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) (h26 : FordLemma26Input) (h51 : FordLemma51Input) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((tupleFinset x H t).card : ℝ)-V t ≤ δ H*tupleNormalization x := by
  obtain ⟨δ₁,hd₁,h₁⟩ := bad_tuple_discard hbox hren hmertens h26
  obtain ⟨δ₂,hd₂,h₂⟩ := good_collision_count h51 hmertens hbox hren
  refine ⟨fun H => δ₁ H+δ₂ H/2,by simpa using hd₁.add (hd₂.div_const 2),?_⟩
  filter_upwards [h₁,h₂,tuple_value_comparison] with H h1 h2 hcomp
  filter_upwards [h1,h2,hcomp] with x h1 h2 hc
  intro t ht
  have h := add_le_add (h1 t ht) (div_le_div_of_nonneg_right (h2 t ht) (by norm_num : (0 : ℝ) ≤ 2))
  exact (hc t).2.trans (h.trans_eq (by unfold tupleNormalization; ring))

/-- The lower half of the main count comparison follows from actual collision
and discard bounds, with no exceptional-value coverage premise. -/
theorem normalized_value_coefficient_lower (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        AH H (fun _ => 1) (theta x)-δ H-ε ≤ normalizedCount V x := by
  obtain ⟨δ₁,hd₁,h₁⟩ := tuple_excess_negligible hbox hren hmertens h26 h51
  obtain ⟨δ₂,hd₂,h₂⟩ := tuple_finite_coefficient_approximation hpnt hbox hmertens hren hconc
    (a := 1) (by norm_num)
  refine ⟨fun H => δ₁ H+δ₂ H,by simpa using hd₁.add hd₂,?_⟩
  filter_upwards [h₁,h₂] with H h1 h2
  intro ε hε
  filter_upwards [h1,h2 (fun _ => 1) (fun _ => ⟨zero_le_one,le_rfl⟩) ε hε,
    scale_eventually_pos,eventually_gt_atTop (1 : ℝ)] with x h1 h2 hnorm hx
  have ht := h2 x (by simp) le_rfl
  rw [weightedTupleCount_one,div_self (ne_of_gt (zero_lt_one.trans hx)),one_mul] at ht
  have he := (div_le_iff₀ hnorm).mpr (h1 x le_rfl)
  rw [sub_div] at he
  change ((tupleFinset x H x).card : ℝ)/tupleNormalization x-V x/tupleNormalization x ≤ δ₁ H at he
  have hlo := (abs_le.mp ht).1
  change _ ≤ V x/tupleNormalization x
  linarith

end TotientAsymptotic

end

end OAI
