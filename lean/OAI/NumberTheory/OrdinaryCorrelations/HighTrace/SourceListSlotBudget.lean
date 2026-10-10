import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CodeEntropyMass
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceLengthGe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GlobalRecord
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceReturnFactor

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

noncomputable def sourceListSlotBudget (C₀ B : ℝ) : ℕ :=
  listCutoff B * (pathLength B * ⌈C₀*Real.log B⌉₊+1)

lemma source_cylinder_prefactor (C₀ A : ℝ) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) :
    ∀ᶠ B : ℝ in atTop,
      Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) ≤ Real.exp B := by
  let a := max A 1
  have ha : 0 < a := zero_lt_one.trans_le (le_max_right _ _)
  have ht := (isLittleO_log_rpow_atTop (by norm_num [rho] : 0 < rho/4)).tendsto_div_nhds_zero
  filter_upwards [RecordPacket.source_entropy_degree_bound C₀ hC₀,
    ht.eventually (eventually_le_nhds (one_div_pos.mpr ha)),eventually_ge_atTop (1:ℝ)] with B hD hlog hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hM : (sourceListSlotBudget C₀ B:ℝ) ≤ B^(1-rho/4) := by
    apply le_trans _ hD
    exact_mod_cast (show sourceListSlotBudget C₀ B ≤ RecordPacket.codeEntropyDegree
      (pathLength B) (listCutoff B)
      (Fintype.card (ExceptionalCodeSlot (pathLength B) ⌈C₀*Real.log B⌉₊
        (listCutoff B) (exceptionalBudget B))) (exceptionalBudget B) from by
      rw [RecordPacket.codeEntropyDegree,exceptionalCodeSlot_card,sourceListSlotBudget]
      omega)
  have hlog0 := Real.log_nonneg hB
  have hlog' := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (rho/4))).mp hlog
  have hp : (sourceListSlotBudget C₀ B:ℝ)*Real.log B ≤ (1/a)*B := by
    calc
      _ ≤ B^(1-rho/4)*((1/a)*B^(rho/4)) := mul_le_mul hM hlog'
        hlog0 (Real.rpow_nonneg hB0.le _)
      _ = _ := by
        rw [mul_left_comm,← Real.rpow_add hB0]
        rw [show (1-rho/4)+rho/4=1 by ring,Real.rpow_one]
  apply Real.exp_le_exp.mpr
  have hsmall : A*(1/a) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one ha).mpr (le_max_left _ _)
  calc
    _ = A*((sourceListSlotBudget C₀ B:ℝ)*Real.log B) := by ring
    _ ≤ A*((1/a)*B) := mul_le_mul_of_nonneg_left hp hA
    _ ≤ B := by nlinarith

lemma source_one_exponential : ∀ᶠ B : ℝ in atTop,
    Real.exp B ≤ B^(eta*(sourceLength B:ℝ)) := by
  have heta : 0 < eta := by norm_num [eta,epsilon]
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1/eta),
    eventually_ge_atTop (2:ℝ)] with B hlog hB
  have hB0 : 0 < B := by linarith
  have hℓ := sourceLength_ge B hB
  rw [Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  have hl := (div_le_iff₀ heta).mp hlog
  have hm := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (sourceLength B))
  nlinarith

namespace GlobalRecord

theorem source_record_sum_with_prefactor (τ T C₀ A : ℝ)
    (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (h : ℕ) (hh : 0 < h) (err : ℝ), err ≤ 1 →
      Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) *
        majorantSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B)
          (hh:=hh) (n:=listCutoff B) (N:=exceptionalBudget B) T err ≤
            B^(-(1+2*eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_global_record_sum τ T C₀ hτ hC₀,
    source_cylinder_prefactor C₀ A hC₀ hA,source_one_exponential,
    eventually_ge_atTop (1:ℝ)] with B hg hc he hB
  intro D h hh err herr
  have hsum0 : 0 ≤ majorantSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B)
      (hh:=hh) (n:=listCutoff B) (N:=exceptionalBudget B) T err :=
    sum_nonneg (fun x _ => traceIntegrationMajorant_nonneg ..)
  have hout := mul_le_mul (hc.trans he) (hg D h hh err herr) hsum0 (Real.rpow_nonneg (zero_le_one.trans hB) _)
  apply hout.trans_eq
  rw [← Real.rpow_add (zero_lt_one.trans_le hB)]
  congr 1
  ring

end GlobalRecord
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
