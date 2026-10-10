import OAI.Analysis.CircleDomains.Modulus.LocalizedTerminalPayment
import OAI.Analysis.CircleDomains.Transfer.TransportedRealLocalization

namespace OAI

/-! The local barrier inequality in an actual real transfer stage. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTransferStage

variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
  (M : RealTransferStage G π σ u a b Flag O K₀ ε)

theorem localized_line_payment
    (T : TerminalComponentAssignment M.terminals.H M.forward M.domain)
    (l : Fin n) {L : ℝ} (hL : 0 ≤ L)
    (hbound : M.domainᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEc : E ⊆ M.core)
    {W : Set ℂ} (hW : MeasurableSet W) (hWB : W ⊆ closedBall 0 L)
    (hWsrc : W ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ M.domain ∧ (horizontalLine y t : Sphere) ∈ M.domain ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction (M.functions l) (M.inverse (horizontalLine y s)) = 0 ∧
      sphereRealFunction (M.functions l) (M.inverse (horizontalLine y t)) = 1 ∧
      ∀ x ∈ Icc s t, (horizontalLine y x : Sphere) ∈ M.domain → horizontalLine y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      ((∫ x in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε) +
      2 * L * (Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε) := by
  let _ : Fintype M.indices := M.finite_indices.fintype
  obtain ⟨hv, _, _⟩ := transported_real_energy M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
  obtain ⟨hi, henergy⟩ := M.transported_energy_away_lt l hE hEc hWsrc
  have hp := T.parallel_line_payment_in_region M.equivalence M.circle_domain
    (M.equivalence.infty_mem_target M.source_infty M.principal.1) hL hbound
    (M.functions l) M.extension_open M.terminal_frontier_extension
    (M.functions_smooth l).continuousOn hv hW hWB hi hJ hcross
  have hosc : Real.sqrt (∑ i : M.indices,
      diam (M.functions l '' frontier (realJordanInterior (M.terminals.H i))) ^ 2) ≤
      Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε := by
    simpa only [terminalOscillation, tsum_fintype] using (M.oscillation l).le
  exact hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy.le)
      (mul_nonneg (Real.sqrt_nonneg _) hL))
    (mul_le_mul_of_nonneg_left hosc (mul_nonneg (by norm_num) hL)))

end CircleDomainRigidity.FiniteTransfer.RealTransferStage

end

end OAI
