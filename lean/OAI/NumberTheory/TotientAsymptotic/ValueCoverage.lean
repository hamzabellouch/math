import OAI.NumberTheory.TotientAsymptotic.BasicCoverage
import OAI.NumberTheory.TotientAsymptotic.PPTStructureInput

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

/-- All uncovered values are controlled by the published Ford extraction
and the independently proved cofactor and elementary exclusions. -/
theorem uncovered_values_negligible (_hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((uncoveredValues x H t).card : ℝ) ≤ (δ H+ε)*tupleNormalization x := by
  obtain ⟨δs,hδs,hstructure⟩ := hstruct
  obtain ⟨δc,hδc,hcof⟩ := cofactor_exception_count hbox hren hmertens
  let δ := fun H => δs (P H)+δc H
  refine ⟨δ,by simpa only [δ,Function.comp_def,zero_add] using (hδs.comp P_tendsto).add hδc,?_⟩
  filter_upwards [hcof,eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)] with H hcof hH hP
  intro ε hε
  filter_upwards [hcof,hstructure (P H) (ε/3) (by positivity),uncovered_values_subset (P_lt_self hH) hP,
    small_values_negligible hren (show 0<ε/3 by positivity),
    omega_values_negligible hmertens hren (show 0<ε/3 by positivity),
    scale_eventually_pos,m_tendsto.eventually (eventually_gt_atTop (P H))] with x hcf he hsub hsmall hω _hn _hm
  intro t ht
  have hcard := (Finset.card_le_card (hsub t ht)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)))
  have hcardR : ((uncoveredValues x H t).card : ℝ) ≤
      ((preimageExceptionValues x (extractedStructureCondition x (P H))).card+(smallValues x).card)+
      ((largeOmegaValues x).card+(cofactorExceptionValues x H).card) := by exact_mod_cast hcard
  change ((preimageExceptionValues x (extractedStructureCondition x (P H))).card : ℝ) ≤ _ at he
  exact hcardR.trans ((add_le_add (add_le_add he hsmall) (add_le_add hω hcf)).trans_eq (by unfold δ; ring))

end TotientAsymptotic

end

end OAI
