import OAI.NumberTheory.TotientAsymptotic.SquareInternalDiscard

namespace OAI

/-! Positive-index squarefree exclusion for every basic witness. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ squareInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsPositiveSquare {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 1 (R x H),
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (remainderPrime η j-1))
      (collisionSmoothCutoff x i)

def positiveSquareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsPositiveSquare η)

lemma squareInternalTuples_card_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (squareInternalTuples x H t).card ≤ (witnessFamily t (squareInternalRemainders x H)).card := by
  have hsub : squareInternalTuples x H t ⊆
      (witnessFamily t (squareInternalRemainders x H)).image (fun q => witnessTuple q.2 q.1) := by
    intro τ hτ
    obtain ⟨hτ,η,hη,he⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    have hw : witnessTuple τ.head η=τ := by
      cases τ
      simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
    refine Finset.mem_image.mpr ⟨(η,τ.head),?_,hw⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hη,Finset.mem_range.mpr (basic_tuple_head_bound hPH hb)⟩,?_⟩
    exact hw.symm ▸ hb
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma positiveSquareFailureTuples_subset : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    positiveSquareFailureTuples x H t ⊆ squareInternalTuples x H t := by
  filter_upwards [square_failure_mem_layer] with H hH
  filter_upwards [hH] with x hx
  intro t τ hτ
  obtain ⟨ht,η,hη,he,i,hi,hfail⟩ := Finset.mem_filter.mp hτ
  have hm := hx i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 η hη hfail
  refine Finset.mem_filter.mpr ⟨ht,η,?_,he⟩
  exact Finset.mem_biUnion.mpr ⟨i,hi,hm⟩

/-- Every basic witness is covered, without choosing a preferred factorization. -/
theorem positive_square_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((positiveSquareFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hsmall⟩ := square_internal_reciprocal_discard hbox hren hmertens
  refine ⟨fun H => 10*δ H,by simpa using hδ.const_mul 10,?_⟩
  filter_upwards [hsmall,positiveSquareFailureTuples_subset,eventually_ge_atTop 2] with H hH hsub hH2
  filter_upwards [hH,hsub,restricted_witness_count,eventually_gt_atTop (1 : ℝ)] with x hx hs hc hx1
  intro t ht
  have hPH := (P_lt_self hH2).le
  have hcoef : 0 ≤ 10*x/Real.log x := div_nonneg (by linarith) (Real.log_pos hx1).le
  calc
    _ ≤ ((squareInternalTuples x H t).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (hs t))
    _ ≤ ((witnessFamily t (squareInternalRemainders x H)).card : ℝ) :=
      Nat.cast_le.mpr (squareInternalTuples_card_le hPH)
    _ ≤ (10*x/Real.log x)*(∑ η ∈ squareInternalRemainders x H, remainderReciprocalWeight η) :=
      hc H hPH t ht _ (fun _ hη => squareInternalRemainders_basic hη)
    _ ≤ (10*x/Real.log x)*(δ H*G x (m x)) := mul_le_mul_of_nonneg_left hx hcoef
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
