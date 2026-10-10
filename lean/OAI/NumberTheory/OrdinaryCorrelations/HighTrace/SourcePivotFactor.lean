import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CenterMassTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FactorialTotal
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FiniteSumInstanceTransfer

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

noncomputable def sourcePivotFactor (τ B : ℝ) : ℝ := ((Real.log 4+1)*τ)/B^(1-eta)

lemma sourcePivotFactor_tendsto (τ : ℝ) :
    Tendsto (sourcePivotFactor τ) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num [eta,epsilon]))

lemma sourcePivotFactor_pos (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) :
    0 < sourcePivotFactor τ B := by
  unfold sourcePivotFactor
  apply div_pos
  · apply mul_pos _ hτ
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · exact Real.rpow_pos_of_pos hB _

lemma inv_le_sourcePivotFactor (τ B : ℝ) (hτ : 1 ≤ τ) (hB : 1 ≤ B) :
    B⁻¹ ≤ sourcePivotFactor τ B := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden : B^(1-eta) ≤ B := by
    conv_rhs => rw [← Real.rpow_one B]
    exact Real.rpow_le_rpow_of_exponent_le hB (by norm_num [eta,epsilon])
  have hC : 1 ≤ (Real.log 4+1)*τ := by
    have hlog := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    nlinarith
  calc
    B⁻¹ = 1/B := (one_div B).symm
    _ ≤ 1/B^(1-eta) := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hB0 _) hden
    _ ≤ _ := div_le_div_of_nonneg_right hC (Real.rpow_pos_of_pos hB0 _).le

theorem source_record_parameters (τ T : ℝ) (hτ : 1 ≤ τ) :
    ∀ᶠ B : ℝ in atTop,
      0 < sourcePivotFactor τ B ∧ sourcePivotFactor τ B ≤ 1 ∧
      Real.exp (-originCharge (sourceSystem B) T) ≤ sourcePivotFactor τ B ∧
      100*Real.log B < returnCharge (sourceSystem B) T ∧
      UnorderedTokenBound (sourceSystem B) (sourcePivotFactor τ B) τ := by
  have hK1 := (sourcePivotFactor_tendsto τ).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hK1,source_charge_harmonic T,
    source_unordered_prime_sum τ (zero_lt_one.trans_le hτ),eventually_ge_atTop (1:ℝ)] with B hK1 hc hp hB
  have hq : Real.log B ≤ originCharge (sourceSystem B) T := by
    have hlog := Real.log_nonneg hB
    dsimp only [originCharge,returnCharge]
    linarith [hc.2]
  refine ⟨sourcePivotFactor_pos τ B (zero_lt_one.trans_le hτ) (zero_lt_one.trans_le hB),hK1,?_,hc.1,hp⟩
  calc
    _ ≤ Real.exp (-Real.log B) := Real.exp_le_exp.mpr (neg_le_neg hq)
    _ = B⁻¹ := by rw [Real.exp_neg,Real.exp_log (zero_lt_one.trans_le hB)]
    _ ≤ _ := inv_le_sourcePivotFactor τ B hτ hB

lemma exp_return_bound (B err q : ℝ) (hB : 0 < B) (hq : 100*Real.log B ≤ q) (r : ℕ) :
    Real.exp (err-q*(r:ℝ)) ≤ Real.exp err * B^(-100*(r:ℝ)) := by
  rw [Real.rpow_def_of_pos hB,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  nlinarith

theorem source_integrated_record_sum (τ T : ℝ) (hτ : 1 ≤ τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (C₀ : ℝ) (D : (sourceSystem B).DivisorFamily B τ C₀)
      (h ℓ L : ℕ) (w₀ : ClosedLine h ℓ) (hh : 0 < h) (r : ℕ)
      (hr₀ : (returnSteps w₀).card=r) (n N : ℕ) (err : ℝ),
      (∑ x : RecordPacket D L w₀ hh r hr₀ n N,
        traceIntegrationMajorant x.line hh x.primitives x.record T err) ≤
        Real.exp err * B^(-100*(r:ℝ)) *
          (sourcePivotFactor τ B)^((goodEdges w₀).card-N) *
            (Fintype.card (ListMetadata ℓ L n):ℝ) *
              RecordPacket.exceptionalCost (sourceSystem B) ℓ L n N C₀ B *
                B^(-(epsilon/10)*((goodEdges w₀).card:ℝ)+epsilon*(badEdges w₀).card) := by
  filter_upwards [source_record_parameters τ T hτ,source_band_nonempty,
    source_center_exponential,eventually_ge_atTop (1:ℝ)] with B hpar hbands hcenter hB
  intro C₀ D h ℓ L w₀ hh r hr₀ n N err
  obtain ⟨pC,hpC⟩ := hbands.1
  obtain ⟨pZ,hpZ⟩ := hbands.2
  have hi := RecordPacket.integrated_record_sum (D := D) (L := L) (w₀ := w₀)
    (hh := hh) (hr₀ := hr₀) (n := n) (N := N) T err (sourcePivotFactor τ B)
    hpar.1 hpar.2.1 hpar.2.2.1 hpar.2.2.2.2 pC pZ hpC hpZ
  apply hi.trans
  have he := exp_return_bound B err (returnCharge (sourceSystem B) T)
    (zero_lt_one.trans_le hB) hpar.2.2.2.1.le r
  have hbc := hcenter (goodEdges w₀).card (badEdges w₀).card
  have hnon : 0 ≤ (sourcePivotFactor τ B)^((goodEdges w₀).card-N) *
      (Fintype.card (ListMetadata ℓ L n):ℝ) * RecordPacket.exceptionalCost (sourceSystem B) ℓ L n N C₀ B :=
    mul_nonneg (mul_nonneg (pow_nonneg hpar.1.le _) (Nat.cast_nonneg _))
      (RecordPacket.exceptionalCost_nonneg ..)
  have hpref := mul_le_mul_of_nonneg_right he hnon
  have hout := mul_le_mul hpref hbc (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (zero_le_one.trans hB) _)) hnon)
  convert hout using 1 <;> ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
