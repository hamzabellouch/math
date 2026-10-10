import OAI.NumberTheory.TotientAsymptotic.SquareDiscard
import OAI.NumberTheory.TotientAsymptotic.OmegaDiscard
import OAI.NumberTheory.TotientAsymptotic.NormalityDiscard
import OAI.NumberTheory.TotientAsymptotic.StrictSlackDiscard

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma badTupleFinset_subset_failures {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    badTupleFinset x H t ⊆ (strictSlackTuples x H t ∪ normalityFailureTuples x H t) ∪
      (squareFailureTuples x H t ∪ omegaFailureTuples x H t) := by
  intro τ hτ
  obtain ⟨η,hη,he,hbad⟩ := bad_tuple_failing_witness hPH hτ
  have ht := (Finset.mem_sdiff.mp hτ).1
  have hprefix : prefixOfRemainder x H η=τ.tail := by
    simpa only [witnessTuple] using congrArg TotientTuple.tail he
  by_cases hs : FailsStrictSlack η
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨ht,η,Finset.mem_filter.mpr ⟨mem_basicRemainderFinset.mpr hη,hs⟩,hprefix⟩))
  by_cases hn : FailsWitnessNormality τ.head η
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨ht,η,hη,hprefix,hn⟩))
  by_cases hsq : FailsWitnessSquare τ.head η
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨ht,η,hη,hprefix,hsq⟩))
  by_cases ho : FailsWitnessOmega η
  · exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨ht,η,hη,hprefix,ho⟩))
  exfalso
  apply hbad
  intro i hi
  refine ⟨?_,?_,?_,?_⟩
  · exact le_of_not_gt (fun h => hs ⟨i,hi,h⟩)
  · intro j hj
    by_contra h
    exact hn ⟨i,hi,j,hj,h⟩
  · by_contra h
    exact hsq ⟨i,hi,h⟩
  · exact le_of_not_gt (fun h => ho ⟨i,hi,h⟩)

theorem bad_tuple_discard (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) (hford : FordLemma26Input) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((badTupleFinset x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ₁,hd₁,h₁⟩ := strict_slack_tuple_discard hbox hren hmertens
  obtain ⟨δ₂,hd₂,h₂⟩ := normality_tuple_discard hbox hren hmertens hford
  obtain ⟨δ₃,hd₃,h₃⟩ := square_tuple_discard hbox hren hmertens
  obtain ⟨δ₄,hd₄,h₄⟩ := omega_tuple_discard hbox hren hmertens
  refine ⟨fun H => (δ₁ H+δ₂ H)+(δ₃ H+δ₄ H),by simpa using (hd₁.add hd₂).add (hd₃.add hd₄),?_⟩
  filter_upwards [h₁,h₂,h₃,h₄,eventually_ge_atTop 2] with H h1 h2 h3 h4 hH
  filter_upwards [h1,h2,h3,h4] with x h1 h2 h3 h4
  intro t ht
  have hPH := (P_lt_self hH).le
  have hc := (Finset.card_le_card (badTupleFinset_subset_failures (x := x) (t := t) hPH)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)))
  have hcR : ((badTupleFinset x H t).card : ℝ) ≤
      ((strictSlackTuples x H t).card+(normalityFailureTuples x H t).card)+
      ((squareFailureTuples x H t).card+(omegaFailureTuples x H t).card) := by exact_mod_cast hc
  exact hcR.trans ((add_le_add (add_le_add (h1 t ht) (h2 t ht))
    (add_le_add (h3 t ht) (h4 t ht))).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
