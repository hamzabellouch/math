import OAI.Geometry.RCD.Sobolev.WeakHamiltonJacobiPairing
import OAI.Geometry.RCD.Sobolev.CompactLaplacian

namespace OAI

/-! # The gradient pairing in a fixed constant gauge

The compact test and its weak Laplacian have zero boundary contribution.
The Laplacian has total mass zero, so the value pairing uses the same
centered potential as the small-noise compactness construction.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem local_centered_hamilton_jacobi_test_pairing
    (w φ : SobolevSpace μ Q) (q ξ : Lp ℝ 2 μ)
    (hq : IsWeakLaplacian μ Q w q) (hξ : IsWeakLaplacian μ Q φ ξ)
    (z : X) {r : ℝ} (hr : 0 < r) (H D : X → ℝ) (ε c : ℝ)
    (hw : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict (closedBall z r)] H)
    (hD : D =ᵐ[μ.restrict (closedBall z r)] fun x => ε/2*q x + localGamma μ Q w w x/2)
    (hφs : ∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q φ x = 0)
    (hξs : ∀ᵐ x ∂μ, x ∉ closedBall z r → ξ x = 0)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ B) :
    (∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x * localGamma μ Q w w x ∂μ) =
      2*(∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x * D x ∂μ) -
      ε*(∫ x in closedBall z r, ξ x * (H x-c) ∂μ) := by
  have hzero : ∫ x, ξ x ∂μ = 0 := integral_weakLaplacian_eq_zero μ Q φ ξ hξ z hr
    (by
      filter_upwards [hφs] with x hx hdist
      apply hx
      intro hm
      have hh : dist z x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hm
      exact (not_lt_of_ge hh) hdist)
    (by
      filter_upwards [hξs] with x hx hdist
      apply hx
      intro hm
      have hh : dist z x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hm
      exact (not_lt_of_ge hh) hdist)
  have hz : ∫ x in closedBall z r, ξ x ∂μ = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero hξs,hzero]
  have hiξ : IntegrableOn ξ (closedBall z r) μ :=
    lp_integrableOn_of_finite μ ξ (closedBall z r) (isCompact_closedBall z r).measure_lt_top.ne
  have hiW : Integrable (fun x => ξ x * SobolevSpace.toLp μ Q w x) μ := by
    simpa only [Real.inner_apply] using
      (L2.integrable_inner (𝕜 := ℝ) ξ (SobolevSpace.toLp μ Q w))
  have hiH : IntegrableOn (fun x => ξ x * H x) (closedBall z r) μ := by
    apply hiW.integrableOn.congr
    filter_upwards [hw] with x hx
    rw [hx]
  have hcenter : (∫ x in closedBall z r, ξ x*(H x-c) ∂μ) =
      ∫ x in closedBall z r, ξ x*H x ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hiH (hiξ.mul_const c),integral_mul_const,hz,zero_mul,sub_zero]
  rw [hcenter]
  exact local_hamilton_jacobi_test_pairing μ Q w φ q ξ hq hξ H D ε hw hD hφs hξs hB

end RegularPointCoordinates

end

end OAI
