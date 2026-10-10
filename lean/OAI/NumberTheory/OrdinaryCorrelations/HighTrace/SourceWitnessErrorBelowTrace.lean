import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EventuallyConstPowLeExp

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

lemma source_witness_error_below_trace : ∀ᶠ B : ℝ in atTop,
    Real.exp (-B^(1+epsilon/2)) ≤ B^(-(1+2*eta)*(sourceLength B:ℝ)) := by
  have hc : 0 < 1/(2*(1+2*eta)) := by norm_num [eta,epsilon]
  have hl := (isLittleO_log_rpow_atTop (by norm_num [epsilon] : 0 < epsilon/2)).tendsto_div_nhds_zero
  filter_upwards [hl.eventually (eventually_le_nhds hc),eventually_ge_atTop (1:ℝ)] with B hlog hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hℓ := sourceLength_le B hB0.le
  have hlog0 := Real.log_nonneg hB
  have hpos : 0 < 2*(1+2*eta) := by norm_num [eta,epsilon]
  have hs := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (epsilon/2))).mp hlog
  have hs' : (2*(1+2*eta))*Real.log B ≤ B^(epsilon/2) := by
    have hh : Real.log B * (2*(1+2*eta)) ≤ B^(epsilon/2) :=
      (le_div_iff₀ hpos).mp (by simpa only [one_div_mul_eq_div] using hs)
    simpa only [mul_comm] using hh
  have hm := mul_le_mul_of_nonneg_left hs' hB0.le
  have hid : B*B^(epsilon/2)=B^(1+epsilon/2) := by rw [Real.rpow_add hB0,Real.rpow_one]
  rw [hid] at hm
  have htt := mul_le_mul_of_nonneg_right hℓ (mul_nonneg (by norm_num [eta,epsilon] : 0 ≤ 1+2*eta) hlog0)
  conv_rhs => rw [Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  nlinarith

namespace NumericalLine

theorem source_retained_allowed_small (h : ℕ) (hh : 0 < h) (τ T C₀ K₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      sourceAllowedRetainedSum D hh K₀ cut ≤ B^(-(1+eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_retained_allowed_with_witness_majorant h hh τ T C₀ K₀ hτ hC₀ hK₀,
    source_witness_majorant_small h hh τ C₀ hτ2 hC₀,source_witness_error_below_trace,
    source_one_exponential,eventually_ge_atTop (2:ℝ)] with B hl hw he hp hB
  intro D cut
  have hB0 : 0 < B := by linarith
  have htwo : (2:ℝ) ≤ B^(eta*(sourceLength B:ℝ)) := by
    apply le_trans _ hp
    have := Real.add_one_le_exp B
    linarith
  calc
    _ ≤ B^(-(1+2*eta)*(sourceLength B:ℝ))+Real.exp (-B^(1+epsilon/2)) :=
      (hl D cut).trans (add_le_add le_rfl (hw D))
    _ ≤ 2*B^(-(1+2*eta)*(sourceLength B:ℝ)) := by linarith
    _ ≤ B^(eta*(sourceLength B:ℝ))*B^(-(1+2*eta)*(sourceLength B:ℝ)) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hB0.le _)
    _ = _ := by rw [←Real.rpow_add hB0]; congr 1; ring
end NumericalLine

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

noncomputable def retainedAllowedKernel (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (D : S.DivisorFamily B τ C₀) (L : ℕ) (G : S.FixedResidues w → Prop) (r : S.Residues) : ℝ :=
  if G ((S.binarySplit w r).1) then S.chronologicalKernel w cut r*allowedIndicator w D L r else 0

lemma retainedAllowedKernel_avg_le (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) :
    |avg (retainedAllowedKernel w cut D L G)| ≤ retainedAllowedIntegral (D:=D) (L:=L) w cut G := by
  rw [avg_equiv (S.binarySplit w),avg_prod]
  have he : (fun a : S.FixedResidues w => avg (fun c : S.FreeResidues w =>
      retainedAllowedKernel w cut D L G ((S.binarySplit w).symm (a,c)))) =
      fun a => if G a then avg (fun c : S.FreeResidues w =>
        S.kernel w cut (mergeResidues w a c)*allowedIndicator w D L (mergeResidues w a c)) else 0 := by
    funext a
    by_cases ha : G a <;>
      simp only [retainedAllowedKernel,Equiv.apply_symm_apply,ha,ite_true,ite_false,
        chronologicalKernel_eq,avg_const,mergeResidues]
  rw [he]
  apply (abs_avg_le _).trans
  apply avg_mono
  intro a
  by_cases ha : G a
  · simp only [ha,ite_true]
    apply le_of_eq
    apply congrArg abs
    congr 1
    exact Subsingleton.elim _ _
  · simp only [ha,ite_false,abs_zero,le_refl]

namespace NumericalLine

noncomputable def fullTraceSum {T : ℝ} (D : S.DivisorFamily B τ C₀)
    (h ℓ L : ℕ) (cut : S.Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ, |avg (fun r => S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r)|

noncomputable def discardedTraceSum {T : ℝ} (D : S.DivisorFamily B τ C₀)
    (h ℓ L : ℕ) (cut : S.Cutoffs T) (G : (w : NumericalLine D h ℓ) → S.FixedResidues w.line → Prop) : ℝ :=
  ∑ w : NumericalLine D h ℓ, avg (fun r => if G w ((S.binarySplit w.line r).1) then 0 else
    |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r|)

lemma fullTraceSum_le_retained_add_discarded {T : ℝ} (D : S.DivisorFamily B τ C₀)
    (cut : S.Cutoffs T) (G : (w : NumericalLine D h ℓ) → S.FixedResidues w.line → Prop) :
    fullTraceSum D h ℓ L cut ≤
      (∑ w : NumericalLine D h ℓ, retainedAllowedIntegral (D:=D) (L:=L) w.line cut (G w)) +
        discardedTraceSum D h ℓ L cut G := by
  unfold fullTraceSum discardedTraceSum
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro w hw
  have he : (fun r => S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r) =
      fun r => retainedAllowedKernel w.line cut D L (G w) r +
        (if G w ((S.binarySplit w.line r).1) then 0 else
          S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r) := by
    funext r
    by_cases hg : G w ((S.binarySplit w.line r).1) <;> simp [retainedAllowedKernel,hg]
  rw [he,OrdinaryCorrelations.SourceCylinder.avg_add']
  apply (abs_add_le _ _).trans
  apply add_le_add (retainedAllowedKernel_avg_le w.line cut (G w))
  apply (abs_avg_le _).trans
  apply avg_mono
  intro r
  split_ifs <;> simp

theorem source_full_trace_with_discarded (h : ℕ) (hh : 0 < h) (τ T C₀ K₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ)) +
          discardedTraceSum D h (sourceLength B) (pathLength B) cut (sourceRetained hh K₀) := by
  filter_upwards [source_retained_allowed_small h hh τ T C₀ K₀ hτ hτ2 hC₀ hK₀] with B hb
  intro D cut
  exact (fullTraceSum_le_retained_add_discarded D cut (sourceRetained hh K₀)).trans
    (add_le_add (hb D cut) le_rfl)

end NumericalLine
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
