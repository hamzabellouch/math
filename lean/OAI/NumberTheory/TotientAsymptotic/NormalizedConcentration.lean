import OAI.NumberTheory.TotientAsymptotic.FullBoxConcentration
import OAI.NumberTheory.TotientAsymptotic.TailCutScale

namespace OAI

/-! The full-dimensional band loss vanishes after both normalization and
the entire discrete-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedBandLoss (K C J c : ℝ) (H : ℕ) : ℝ :=
  Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
    projectedEnvelope J (P H)*((Real.exp (-c/2))^H/(1-Real.exp (-c/2)))

lemma normalizedBandLoss_tendsto (K C : ℝ) {J c : ℝ} (hJ : 0 < J) (hc : 0 < c) :
    Tendsto (normalizedBandLoss K C J c) atTop (nhds 0) := by
  have h1 := (Real.continuous_exp.tendsto (0 : ℝ)).comp ((simplexBoxTail_tendsto 4).comp P_tendsto)
  have h2 := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have h3 := cofactor_concentration_tail_tendsto K hc
  have hh := ((h1.mul_const C).mul h2).mul h3
  have he : (fun H => normalizedBandLoss K C J c H) =
      (fun H => (Real.exp (simplexBoxTail 4 (P H))*C*projectedEnvelope J (P H))*
        (Real.exp (K*cofactorScale H)*(Real.exp (-c/2))^H/(1-Real.exp (-c/2)))) := by
    funext H
    unfold normalizedBandLoss
    ring
  change Tendsto (fun H => normalizedBandLoss K C J c H) atTop (nhds 0)
  rw [he]
  simpa only [Function.comp_def, Real.exp_zero, mul_zero, zero_mul] using hh

/-- For every fixed cofactor exponent, Ford concentration removes all
retained phase bands with an error tending to zero as the tail cut grows. -/
theorem normalized_retained_band_loss (hford : FordCoordinateConcentrationInput)
    (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        ∀ N : ℕ, L x H=N+2 → ∀ hRN : R x H ≤ N+2,
        Real.exp (K*cofactorScale H)*volume.real (retainedPhaseBad x H (N+2) hRN) /
          G x (m x) ≤ δ H := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := full_box_retained_concentration hford
  obtain ⟨J, hJ, hproj⟩ := uniform_projected_volume_bound hren
  refine ⟨normalizedBandLoss K C J c, normalizedBandLoss_tendsto K C hJ hc, ?_⟩
  have hsmall : ∀ᶠ H : ℕ in atTop, Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) := by
    have ht := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4)
    exact (ht.eventually (eventually_lt_nhds (by norm_num : Real.exp (0 : ℝ)<102/100))).mono
      (fun _ h => h.le)
  filter_upwards [eventually_tail_cut_separated, hsmall] with H hcuts hsmallH
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)), phase_band_center_close,
    hproj, m_tendsto.eventually (eventually_ge_atTop (N₀+P H+2)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hB hcenter hpr hmN hHm
  intro N hdim hRN
  have hN : N₀ ≤ N := by unfold L at hdim; omega
  have hdim' : m x-P H=N+2 := hdim
  have hv := hconc hN hB hHm hdim' hcuts.2.1 hcuts.2.2.1 hcuts.2.2.2 hsmallH hcenter hRN
  have hPm : P H ≤ m x := by omega
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hpr (P H) hPm)
  change G x (L x H) ≤ _ at hG
  rw [hdim] at hG
  have hq : Real.exp (-c/2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo : 0 ≤ (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) :=
    div_nonneg (pow_pos (Real.exp_pos _) _).le (sub_pos.mpr hq).le
  have hA : 0 ≤ Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
      ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))) := by positivity
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  calc
    _ ≤ Real.exp (K*cofactorScale H)*
        ((Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
          ((Real.exp (-c/2))^H/(1-Real.exp (-c/2)))) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ = (Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
        ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))))*G x (N+2) := by ring
    _ ≤ (Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
        ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))))*
        (projectedEnvelope J (P H)*G x (m x)) := mul_le_mul_of_nonneg_left hG hA
    _ = _ := by unfold normalizedBandLoss; ring

end TotientAsymptotic

end

end OAI
