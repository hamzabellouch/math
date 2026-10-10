import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceLengthGe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ReturnCountLe

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

lemma source_return_factor : ∀ᶠ B : ℝ in atTop,
    (sourceLength B:ℝ)+1 ≤ B^(eta*(sourceLength B:ℝ)) := by
  filter_upwards [source_topology_prefactor,eventually_ge_atTop (10000000:ℝ)] with B hs hB
  have hB1 : 1 ≤ B := by linarith
  have hl := sourceLength_ge B (by linarith)
  calc
    _ ≤ B^2 := hs.1
    _ = B^(2:ℝ) := (Real.rpow_two B).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num [eta,epsilon] at *; linarith)

namespace GlobalRecord

theorem source_global_record_sum (τ T C₀ : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (h : ℕ) (hh : 0 < h) (err : ℝ), err ≤ 1 →
      majorantSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B)
        (hh:=hh) (n:=listCutoff B) (N:=exceptionalBudget B) T err ≤
          B^(-(1+3*eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_topology_fiber_bound τ T C₀ hτ hC₀,source_return_factor,
    eventually_ge_atTop (1:ℝ)] with B hs hreturn hB
  intro D h hh err herr
  let ℓ := sourceLength B
  let W := B^(-(1+4*eta)*(ℓ:ℝ))
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hW : 0 ≤ W := Real.rpow_nonneg hB0.le _
  have hrow (r : Fin (ℓ+1)) :
      (∑ t : Topology ℓ r.val,
        ∑ x : Fiber (D:=D) (L:=pathLength B) (h:=h) (hh:=hh)
          (n:=listCutoff B) (N:=exceptionalBudget B) r.val t,
          traceIntegrationMajorant x.val.line hh x.val.primitives x.val.record T err) ≤ W := by
    let C := (4:ℝ)^ℓ*((ℓ:ℝ)+1)^r.val
    have hC : 0 < C := by dsimp [C]; positivity
    have hf (t : Topology ℓ r.val) :
        (∑ x : Fiber (D:=D) (L:=pathLength B) (h:=h) (hh:=hh)
          (n:=listCutoff B) (N:=exceptionalBudget B) r.val t,
          traceIntegrationMajorant x.val.line hh x.val.primitives x.val.record T err) ≤ W/C := by
      apply (le_div_iff₀ hC).mpr
      by_cases hx : Nonempty (Fiber (D:=D) (L:=pathLength B) (h:=h) (hh:=hh)
          (n:=listCutoff B) (N:=exceptionalBudget B) r.val t)
      · let x₀ := Classical.choice hx
        have hp := fiber_sum_le r.val t x₀ T err
        have hr := hs D h x₀.val.line hh r.val x₀.property.choose err herr
        exact (mul_le_mul_of_nonneg_right hp hC.le).trans (by simpa only [mul_comm,C,W,ℓ] using hr)
      · have : IsEmpty (Fiber (D:=D) (L:=pathLength B) (h:=h) (hh:=hh)
          (n:=listCutoff B) (N:=exceptionalBudget B) r.val t) := not_nonempty_iff.mp hx
        simpa only [sum_of_isEmpty,zero_mul] using hW
    have hc : (Fintype.card (Topology ℓ r.val):ℝ) ≤ C := by
      dsimp only [C]
      exact_mod_cast topology_card ℓ r.val
    calc
      _ ≤ ∑ _t : Topology ℓ r.val, W/C := sum_le_sum (fun t _ => hf t)
      _ = (Fintype.card (Topology ℓ r.val):ℝ)*(W/C) := by simp
      _ ≤ C*(W/C) := mul_le_mul_of_nonneg_right hc (div_nonneg hW hC.le)
      _ = W := mul_div_cancel₀ _ hC.ne'
  rw [majorantSum_partition]
  calc
    _ ≤ ∑ _r : Fin (ℓ+1), W := sum_le_sum (fun r _ => hrow r)
    _ = ((ℓ:ℝ)+1)*W := by simp
    _ ≤ B^(eta*(ℓ:ℝ))*W := mul_le_mul_of_nonneg_right hreturn hW
    _ = _ := by
      dsimp only [W]
      rw [← Real.rpow_add hB0]
      congr 1
      ring

end GlobalRecord
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
