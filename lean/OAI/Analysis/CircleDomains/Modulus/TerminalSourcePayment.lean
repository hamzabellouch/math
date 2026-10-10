import OAI.Analysis.CircleDomains.Modulus.TerminalLinePayment
import OAI.Analysis.CircleDomains.Sobolev.TransportedRealEnergy

namespace OAI

/-!
# Line payment charged to the physical source

The target energy in the finite-hole inequality is bounded by the actual
source metric energy. Boundary tolls are the physical terminal-boundary
diameters, as in the real-coordinate finite transfer.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.parallel_line_payment_source_energy
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ openCompletedRegion T)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ)
    (hw : ContDiffOn ℝ ∞ w (realChartDomain (openCompletedRegion T)))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hwO : ContinuousOn w O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain (openCompletedRegion T), (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain (openCompletedRegion T)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V ∧ (horizontalLine y t : Sphere) ∈ V ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (horizontalLine y s)) = 0 ∧
      sphereRealFunction w (fi (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain (openCompletedRegion T), gradientEnergy w g x) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  have hU := isOpen_openCompletedRegion T
  obtain ⟨hv, _, _⟩ := transported_real_energy heq hU hV.1 hinf hfix w hw hmetric hg hi
  obtain ⟨hlocal, hle⟩ := transported_real_energy_on_disk_le heq hU hV.1 hinf hfix
    w hw hmetric hg hi L
  have hp := a.parallel_line_payment heq hV (heq.infty_mem_target hinf hfix)
    hL hbound w hO hTO hwO hv hlocal hJ hcross
  exact hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle)
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

end CircleDomainRigidity

end

end OAI
