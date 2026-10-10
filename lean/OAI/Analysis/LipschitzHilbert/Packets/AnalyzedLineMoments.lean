import OAI.Analysis.LipschitzHilbert.Packets.AnalyzedLineFamily
import OAI.Analysis.LipschitzHilbert.Packets.PacketLineConcentration

namespace OAI

/-! Reference-line moments for the actual analyzing coefficients, using
their norm bound and local Carleson budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert
namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem analyzedLine_moment (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ)
      (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
         lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      ∀ grid : FiniteLineGrid, 1 < grid.branching → P.topLength ≤ grid.width →
      ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |(P.analyzedLine d v hv g hg hg1 y hderiv).variation x|)^p
        ∂grid.lineMeasure) ≤
      (2:ℝ≥0∞)^p *
        (7 * ENNReal.ofReal ((p * (((grid.branching:ℝ)+2) *
          (2 * Real.sqrt (M * P.constant^2 *
            (A * P.constant^2 * P.coefficientScale⁻¹^2) + 1) +
            4 * (P.constant * (4 * Real.pi)^2))) / Real.log (3/2))^p) +
          (ENNReal.ofReal (Real.sqrt (M * P.constant^2 *
            (A * P.constant^2 * P.coefficientScale⁻¹^2) + 1)))^p) * grid.lineMeasure Set.univ := by
  obtain ⟨A,hA,hbudget⟩ := analyzedLine_localBudget (N := N) (κ := κ) (ι := ι) hL hlo hhi
  obtain ⟨M,hM,hmoment⟩ := LinePacketFamily.line_moment (N := N) (κ := κ) (ι := ι) hL hlo hhi
  refine ⟨A,M,hA,hM,?_⟩
  intro P d v hv g hg hg1 y hderiv hd hlow hhigh grid hb hwidth p hp
  exact hmoment (P.analyzedLine d v hv g hg hg1 y hderiv)
    (A * P.constant^2 * P.coefficientScale⁻¹^2) (by positivity)
    (hbudget P d v hv g hg hg1 y hderiv hd hlow hhigh)
    (fun j i k ξ hξ => hlow j i k y ξ hξ)
    (fun j i k ξ hξ => hhigh j i k y ξ hξ) grid hb hwidth p hp

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
