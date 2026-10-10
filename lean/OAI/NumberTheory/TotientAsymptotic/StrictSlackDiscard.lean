import OAI.NumberTheory.TotientAsymptotic.StrictSlackEnclosure
import OAI.NumberTheory.TotientAsymptotic.NormalizedStrictSlack
import OAI.NumberTheory.TotientAsymptotic.RestrictedPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.RestrictedWitnessCount

namespace OAI

/-! The actual tuple discard caused by failure of the strict-slack condition. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def strictSlackRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter FailsStrictSlack

def strictSlackTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ strictSlackRemainders x H,
    prefixOfRemainder x H η=τ.tail)

lemma strictSlackTuples_card_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (strictSlackTuples x H t).card ≤ (witnessFamily t (strictSlackRemainders x H)).card := by
  have hsub : strictSlackTuples x H t ⊆
      (witnessFamily t (strictSlackRemainders x H)).image (fun q => witnessTuple q.2 q.1) := by
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

theorem strict_slack_reciprocal_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ η ∈ strictSlackRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨C,hC,hcof⟩ := tail_cofactor_sum hmertens
  obtain ⟨D,hD,hprime⟩ := restricted_prime_mass_bound hbox
  obtain ⟨δ,hδ,hshell⟩ := normalized_strict_slack_shell hren (4*(lam/rho))
  let ε := fun H => C*(1+bandPrimeError D (9/10) (P H))*δ H
  have he : Tendsto ε atTop (nhds 0) := by
    have hb := (bandPrimeError_tendsto D (by norm_num : (0 : ℝ) < 9/10)).comp P_tendsto
    simpa only [ε,Function.comp_def,add_zero,mul_zero] using
      (((tendsto_const_nhds.add hb).const_mul C).mul hδ)
  refine ⟨ε,he,?_⟩
  filter_upwards [hshell,eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hH hH2 hP
  have hPH := P_lt_self hH2
  filter_upwards [hH,theta_eventually_mem,B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hx hs hB hHm
  let S := strictSlackRemainders x H
  let Q := S.image RemainderDatum.primes
  let T := strictSlackShell x (R x H) (L x H) (by unfold R L; omega)
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  have hL : 0 < L x H := by unfold L; omega
  have hp := hprime hs.1 (hPH.le.trans hHm) Q T hQ (strictSlackShell_volume_ne_top x _ hL)
    (by
      intro p hp v hd
      obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
      exact failing_remainder_box_enclosure hPH hHm hP hB.le (hS η hη)
        (Finset.mem_filter.mp hη).2 hd)
  have hc : (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹) ≤
      C*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [cofactorScale,mul_assoc] using hcof H
  have hf : 0 ≤ 1+bandPrimeError D (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hD.le (by norm_num : (0 : ℝ) < 9/10) (P H)]
  have hv : Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T ≤ δ H*G x (m x) :=
    (div_le_iff₀ (G_pos hB (m x))).mp (hx _)
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ∑ p ∈ Q, reciprocalShiftWeight p :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError D (9/10) (P H))*volume.real T) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (C*(1+bandPrimeError D (9/10) (P H)))*
        (Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T) := by ring
    _ ≤ (C*(1+bandPrimeError D (9/10) (P H)))*(δ H*G x (m x)) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg hC.le hf)
    _ = _ := by dsimp [ε]; ring

theorem strict_slack_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, t ≤ x →
      ((strictSlackTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hsmall⟩ := strict_slack_reciprocal_mass hbox hren hmertens
  refine ⟨fun H => 10*δ H,by simpa using hδ.const_mul 10,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 2] with H hH hH2
  have hPH := (P_lt_self hH2).le
  filter_upwards [hH,restricted_witness_count,eventually_gt_atTop (1 : ℝ)] with x hx hcount hx1
  intro t ht
  have hc : 0 ≤ 10*x/Real.log x := by
    exact div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hx1).le) (Real.log_pos hx1).le
  calc
    _ ≤ ((witnessFamily t (strictSlackRemainders x H)).card : ℝ) :=
      Nat.cast_le.mpr (strictSlackTuples_card_le hPH)
    _ ≤ (10*x/Real.log x)*(∑ η ∈ strictSlackRemainders x H, remainderReciprocalWeight η) :=
      hcount H hPH t ht _ (by
        intro η hη
        exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1)
    _ ≤ (10*x/Real.log x)*(δ H*G x (m x)) := mul_le_mul_of_nonneg_left hx hc
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
