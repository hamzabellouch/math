import OAI.Analysis.CircleDomains.Modulus.TerminalSourcePayment
import OAI.Analysis.CircleDomains.Modulus.TerminalNormBudget

namespace OAI

/-!
# Limiting payment by source energy and band widths

For a fixed barrier the transfer errors vanish while the original source
energy and band norm remain. This is the limit required before choosing
successively smaller barriers in the unmarked-end argument.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem limiting_terminal_line_payment
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ) (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (a : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    (hinf : ∀ n, OnePoint.infty ∈ openCompletedRegion (T n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : ℕ → (ℝ × ℝ) → ℝ)
    (hw : ∀ n, ContDiffOn ℝ ∞ (w n) (realChartDomain (openCompletedRegion (T n))))
    (O : ℕ → Set (ℝ × ℝ)) (hO : ∀ n, IsOpen (O n))
    (hTO : ∀ n i, frontier (realJordanInterior (T n i)) ⊆ O n)
    (hwO : ∀ n, ContinuousOn (w n) (O n))
    (g : ℕ → (ℝ × ℝ) → PlanarMetric)
    (hmetric : ∀ n p, p ∈ openCompletedRegion (T n) → IsMetricConformalAt (g n) (f n) p)
    (hg : ∀ n x, x ∈ realChartDomain (openCompletedRegion (T n)) → (g n x).PosDef)
    (hi : ∀ n, IntegrableOn (gradientEnergy (w n) (g n))
      (realChartDomain (openCompletedRegion (T n))))
    (band : (n : ℕ) → I n → ℝ) (hband : ∀ n i, 0 ≤ band n i)
    {E B : ℝ} (hE : 0 ≤ E)
    (hbandnorm : ∀ n, Real.sqrt (∑ i, band n i ^ 2) ≤ B)
    (e δ : ℕ → ℝ) (he : Tendsto e atTop (𝓝 (E ^ 2))) (hδ : Tendsto δ atTop (𝓝 0))
    (henergy : ∀ᶠ n in atTop,
      (∫ x in realChartDomain (openCompletedRegion (T n)), gradientEnergy (w n) (g n) x) ≤ e n)
    (hexcess : ∀ᶠ n in atTop, Real.sqrt (∑ i,
      max (diam (w n '' frontier (realJordanInterior (T n i))) - band n i) 0 ^ 2) ≤ δ n)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V n ∧ (horizontalLine y t : Sphere) ∈ V n ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction (w n) (fi n (horizontalLine y s)) = 0 ∧
      sphereRealFunction (w n) (fi n (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * E + 2 * L * B := by
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (e n) + 2 * L * (B + δ n) := by
    filter_upwards [hcross, henergy, hexcess] with n hn hnE hnA
    have hp := (a n).parallel_line_payment_source_energy (heq n) (hV n)
      (hinf n) (hfix n) hL (hbound n) (w n) (hw n) (hO n) (hTO n) (hwO n)
      (hmetric n) (hg n) (hi n) hJ hn
    have hcost := sqrt_sum_sq_le_of_excess_budget
      (fun i => diam (w n '' frontier (realJordanInterior (T n i)))) (band n)
      (fun _ => diam_nonneg) (hband n) (hbandnorm n) hnA
    exact hp.trans (add_le_add
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnE)
        (mul_nonneg (Real.sqrt_nonneg _) hL))
      (mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num) hL)))
  have hs : Tendsto (fun n => Real.sqrt (e n)) atTop (𝓝 E) := by
    simpa only [Function.comp_def, Real.sqrt_sq hE] using
      Real.continuous_sqrt.continuousAt.tendsto.comp he
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (e n) +
      2 * L * (B + δ n)) atTop (𝓝 (Real.sqrt Real.pi * L * E + 2 * L * B)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.mul hs).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.add hδ))
  exact ge_of_tendsto ht hpay

end CircleDomainRigidity

end

end OAI
