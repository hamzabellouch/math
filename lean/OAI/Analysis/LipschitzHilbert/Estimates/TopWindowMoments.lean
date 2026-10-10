import OAI.Analysis.LipschitzHilbert.Packets.TopPacketWindow
import OAI.Analysis.LipschitzHilbert.Fourier.UniformLineMoments

namespace OAI

/-! The two-coordinate top weight preserves uniform line moments.
The constant is chosen before all finite packet spaces and scale counts. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.TopPacketWindow

theorem line_moment (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ (q : ℕ) (T : TopPacketWindow P q) (grid : FiniteLineGrid),
      1 < grid.branching → P.topLength ≤ grid.width → ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |(polynomialWeight T.baseX T.radiusX q x *
        polynomialWeight T.baseZ T.radiusZ q P.lineY) * P.variation x|)^p ∂grid.lineMeasure) ≤
      (2:ℝ≥0∞)^p * (7 * ENNReal.ofReal
        ((p * (((grid.branching:ℝ)+2) *
          (2*Real.sqrt (A*T.constant^2*B+1) + 4*(T.constant*(4*Real.pi)^2))) /
            Real.log (3/2))^p) +
        (ENNReal.ofReal (Real.sqrt (A*T.constant^2*B+1)))^p) * grid.lineMeasure Set.univ := by
  obtain ⟨A,hA,hM⟩ := LinePacketFamily.uniform_line_moment hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh q T grid hb hg p hp
  have hl : ∀ j i k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (T.family.wave j i k) ξ = 0 := by
    intro j i k ξ hξ
    exact topWeightedWave_low (P.wave j i k) T.baseX T.radiusX T.baseZ T.radiusZ P.lineY q
      _ _ (hlow j i k) (hhigh j i k) ξ hξ
  have hh : ∀ j i k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (T.family.wave j i k) ξ = 0 := by
    intro j i k ξ hξ
    exact topWeightedWave_high (P.wave j i k) T.baseX T.radiusX T.baseZ T.radiusZ P.lineY q
      _ _ (hlow j i k) (hhigh j i k) ξ hξ
  have hm := hM N κ ι T.family B hB (T.family_budget B hbudget) hl hh grid hb hg p hp
  have hC : T.family.constant = T.constant := rfl
  rw [hC] at hm
  simpa only [family_variation] using hm

end LipschitzHilbert.TopPacketWindow

end

end OAI
