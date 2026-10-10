import OAI.NumberTheory.TotientAsymptotic.HeadSquareDiscard
import OAI.NumberTheory.TotientAsymptotic.PositiveSquareDiscard

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def FailsWitnessSquare {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1))
      (collisionSmoothCutoff x i)

def squareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessSquare τ.head η)

lemma squareFailureTuples_subset (x t : ℝ) (H : ℕ) :
    squareFailureTuples x H t ⊆ headSquareFailureTuples x H t ∪ positiveSquareFailureTuples x H t := by
  intro τ hτ
  obtain ⟨ht,η,hη,he,i,hi,hfail⟩ := Finset.mem_filter.mp hτ
  by_cases hi0 : i=0
  · subst i
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,η,hη,he,hfail⟩)
  · apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨ht,η,hη,he,i,Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hi).2⟩,?_⟩
    have hprod : (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime τ.head η j-1)) =
        ∏ j ∈ Finset.Icc i (collisionLastIndex x i), (remainderPrime η j-1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
      simp only [wholeWitnessPrime,ite_eq_right hj0]
    rwa [hprod] at hfail

theorem square_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((squareFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hpos⟩ := positive_square_tuple_discard hbox hren hmertens
  obtain ⟨γ,hγ,hhead⟩ := head_square_tuple_discard hren hmertens
  refine ⟨fun H => γ H+δ H,by simpa using hγ.add hδ,?_⟩
  filter_upwards [hpos,hhead] with H hH hh
  filter_upwards [hH,hh] with x hp hh
  intro t ht
  have hc := (Finset.card_le_card (squareFailureTuples_subset x t H)).trans (Finset.card_union_le _ _)
  have hcR : ((squareFailureTuples x H t).card : ℝ) ≤
      (headSquareFailureTuples x H t).card+(positiveSquareFailureTuples x H t).card := by exact_mod_cast hc
  exact hcR.trans ((add_le_add (hh t ht) (hp t ht)).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
