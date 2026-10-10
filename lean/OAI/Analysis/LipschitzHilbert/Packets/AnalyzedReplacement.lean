import OAI.Analysis.LipschitzHilbert.Packets.UniformAnalyzedLine
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement

namespace OAI

/-! Replacement synthesis packets retain the local budget of the actual
integral-defined analyzing coefficients. The same coefficient budget applies to top weights and covariant
derivative packets. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert.PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def analyzedReplacement (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ)
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant/P.length j)*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y))
    (C : ℝ) (hC : 0 < C) (wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (hb : ∀ j i k x, ‖wave j i k x‖ ≤ C*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y))
    (hdb : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤ (C/P.length j)*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y)) : LinePacketFamily N κ ι :=
  (P.analyzedLine d v hv g hg hg1 y hderiv).replaceWaves C hC wave hb hdb

theorem uniform_analyzedReplacement_budget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ) (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
          lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      ∀ C hC wave hb hdb,
      (P.analyzedReplacement d v hv g hg hg1 y hderiv C hC wave hb hdb).HasLocalBudget
        (A*P.constant^2*P.coefficientScale⁻¹^2) := by
  obtain ⟨A,hA,hbudget⟩ := uniform_analyzedLine_localBudget hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 y hderiv hd hlo' hhi' C hC wave hb hdb
  exact hbudget N κ ι P d v hv g hg hg1 y hderiv hd hlo' hhi'

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
