import OAI.NumberTheory.TotientAsymptotic.OmegaInternalDiscard

namespace OAI

/-! The complete residual factor-count exclusion for universally good tuples. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ omegaInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsWitnessOmega {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    fordBandScale x i/((m x-i : ℕ) : ℝ)^8 < ((collisionResidual η i).primeFactorsList.length : ℝ)

def omegaFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessOmega η)

lemma omegaInternalRemainders_basic {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : η ∈ omegaInternalRemainders x H) :
    IsBasicRemainder x H η := by
  obtain ⟨i,_,hj⟩ := Finset.mem_biUnion.mp hη
  obtain ⟨j,_,hη⟩ := Finset.mem_biUnion.mp hj
  exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1

lemma omegaInternalTuples_card_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (omegaInternalTuples x H t).card ≤ (witnessFamily t (omegaInternalRemainders x H)).card := by
  have hsub : omegaInternalTuples x H t ⊆
      (witnessFamily t (omegaInternalRemainders x H)).image (fun q => witnessTuple q.2 q.1) := by
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

lemma omegaFailureTuples_subset : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    omegaFailureTuples x H t ⊆ omegaInternalTuples x H t := by
  filter_upwards [omega_failure_large_shift] with H hH
  filter_upwards [hH] with x hx
  intro t τ hτ
  obtain ⟨ht,η,hη,he,i,hi,hfail⟩ := Finset.mem_filter.mp hτ
  obtain ⟨j,hj,hbad⟩ := hx i (Finset.mem_Icc.mp hi).2 η hη hfail
  refine Finset.mem_filter.mpr ⟨ht,η,?_,he⟩
  exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_biUnion.mpr
    ⟨j,hj,Finset.mem_filter.mpr ⟨mem_basicRemainderFinset.mpr hη,hbad⟩⟩⟩

/-- Every basic witness is covered, without choosing a preferred factorization. -/
theorem omega_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((omegaFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hsmall⟩ := omega_internal_reciprocal_discard hbox hren hmertens
  refine ⟨fun H => 10*δ H,by simpa using hδ.const_mul 10,?_⟩
  filter_upwards [hsmall,omegaFailureTuples_subset,eventually_ge_atTop 2] with H hH hsub hH2
  filter_upwards [hH,hsub,restricted_witness_count,eventually_gt_atTop (1 : ℝ)] with x hx hs hc hx1
  intro t ht
  have hPH := (P_lt_self hH2).le
  have hcoef : 0 ≤ 10*x/Real.log x := div_nonneg (by linarith) (Real.log_pos hx1).le
  calc
    _ ≤ ((omegaInternalTuples x H t).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (hs t))
    _ ≤ ((witnessFamily t (omegaInternalRemainders x H)).card : ℝ) :=
      Nat.cast_le.mpr (omegaInternalTuples_card_le hPH)
    _ ≤ (10*x/Real.log x)*(∑ η ∈ omegaInternalRemainders x H, remainderReciprocalWeight η) :=
      hc H hPH t ht _ (fun _ hη => omegaInternalRemainders_basic hη)
    _ ≤ (10*x/Real.log x)*(δ H*G x (m x)) := mul_le_mul_of_nonneg_left hx hcoef
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
