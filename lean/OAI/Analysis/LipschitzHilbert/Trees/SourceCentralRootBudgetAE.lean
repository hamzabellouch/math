import OAI.Analysis.LipschitzHilbert.Trees.SourceRootIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralBudgetAE

namespace OAI

/-! The normalized root moments give the negative-power estimate for
the exact boundary-weighted central packet sum. The actual finite root
partition costs only two, absorbed by one further power of L. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem eventually_source_central_sum_gain_ae (d q Q : ℝ)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass S : ℝ), 0 < Nmass → 0 < Fmass → 0 ≤ S →
      L/2 ≤ Real.log Nmass → μ.real Set.univ ≤ Fmass → S ≤ L^q*Nmass^2*Fmass →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
      (∀ᵐ x ∂μ, (∑ t ∈ tops, weight t x) ≤ L^q*Nmass) →
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let beta := ((1+PhaseCombinatorics.phaseParameter D)/p)/(K:ℝ)
    let n := fun c => g.mass tops slope precision cutoff weight 0 c
    let amp := fun c x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) (fun _ => (beta:ℂ)) beta x 0 c
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      Integrable (fun x => ‖(n c x^(alpha/p-1)) • amp c x‖^p) μ) →
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      (∫ x, ‖(n c x^(alpha/p-1)) • amp c x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p)) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) beta x:ℝ):ℂ) • value x s
    Integrable (fun x => ‖W x‖) μ ∧ (∫ x, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_source_central_integral_gain_ae d q (Q+1) hd hq (by positivity),
    eventually_ge_atTop (2:ℝ)] with L hgain hL
  intro D hD hDL μ _ g tops slope precision cutoff weight hp hw hwmeas gap packets
    assigned stop value hv hassigned heligible start Nmass Fmass S hN hF hS hlogN
    hmeasure hSbound hslope htotal K p alpha beta n amp henergy hmoment W
  have hL0 : 0 < L := by linarith
  have hK : 0 < K := SourceParameters.blockCount_pos (by linarith)
  let B := L^(-(Q+1))*Nmass*Fmass
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hroot (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) :
      Integrable (fun x => n c x^beta*‖amp c x‖) μ ∧
        (∫ x, n c x^beta*‖amp c x‖ ∂μ) ≤ B := by
    have hnpos : ∀ x, 0 < n c x := by
      obtain ⟨t,ht⟩ := (g.mem_sourceRootCells tops slope precision cutoff c).mp hc
      intro x
      exact g.mass_pos_of_member tops slope precision cutoff weight hw 0 c x ht
    have hnupper : ∀ᵐ x ∂μ, n c x ≤ L^q*Nmass := by
      filter_upwards [htotal] with x hx
      exact (g.mass_le_total tops slope precision cutoff weight
        (fun t x => (hw t x).le) 0 c x).trans hx
    exact hgain D hD hDL X κ μ (n c) (amp c) Nmass Fmass S hN hF hS hlogN
      hnpos hnupper (g.measurable_mass tops slope precision cutoff weight hwmeas 0 c)
      (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
        packets assigned stop value hv _ beta 0 c) hmeasure hSbound (henergy c hc) (hmoment c hc)
  have heq (c : ℤ) (x : X) :
      ‖((n c x^beta:ℝ):ℂ) • amp c x‖ = n c x^beta*‖amp c x‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le) 0 c x) _)]
  have hs := g.sourceBoundarySum_integral_le μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible beta start B hB hslope
    (fun c hc => by
      change Integrable (fun x => ‖((n c x^beta:ℝ):ℂ) • amp c x‖) μ
      simpa only [heq] using (hroot c hc).1)
    (fun c hc => by
      change (∫ x, ‖((n c x^beta:ℝ):ℂ) • amp c x‖ ∂μ) ≤ B
      simpa only [heq] using (hroot c hc).2)
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hpower : 2*L^(-(Q+1)) ≤ L^(-Q) := by
    calc
      2*L^(-(Q+1)) ≤ L*L^(-(Q+1)) :=
        mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
      _ = L^(-Q) := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hL0]
        congr 1
        ring
  dsimp only [B]
  calc
    2*(L^(-(Q+1))*Nmass*Fmass) = (2*L^(-(Q+1)))*Nmass*Fmass := by ring
    _ ≤ L^(-Q)*Nmass*Fmass := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpower hN.le) hF.le

end LipschitzHilbert.AngularGrid

end

end OAI
