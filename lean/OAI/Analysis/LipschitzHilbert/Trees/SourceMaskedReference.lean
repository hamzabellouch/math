import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskedLine
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceBounds

namespace OAI

/-! The reference square and cubic-variation moments for actual masked
synthesis. The original analyzing budget is retained; the synthesis
constant doubles and the annulus is relaxed by half its lower endpoint. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.LinePacketFamily

 theorem sinc_masked_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j u k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k) xi = 0) →
      (∀ j u k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j u k) xi = 0) →
      ∀ (n : ℕ) (a b c d : ∀ j, ι j → κ → ℝ)
        (hrate : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j),
      (∀ j u k, (2*(n:ℝ))*((|a j u k|+|c j u k|)/(2*Real.pi)) ≤
        (lo/2)*(2:ℝ)^j.val) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ grid.width) → ∀ p : ℝ, 0 ≤ p →
      let Q := P.sincMasked n a b c d hrate
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        SourceLatticePacket.referenceSquareMomentCost B grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        SourceLatticePacket.referenceVariationMomentCost M (2*P.constant) B grid p*grid.lineMeasure univ := by
  obtain ⟨M,hM,hmoment⟩ := uniform_line_moment_of_supported hL (half_pos hlo)
    (add_nonneg hhi (half_pos hlo).le)
  refine ⟨M,hM,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh n a b c d hrate hband grid hb hwidth p hp
  let Q := P.sincMasked n a b c d hrate
  have hQ : Q.HasLocalBudget B := P.sincMasked_budget n a b c d hrate hbudget
  have hwidth' : ∀ j (_u : ι j), Q.length j ≤ grid.width := hwidth
  obtain ⟨hl,hh⟩ := P.sincMasked_cutoffs n a b c d hrate lo hi (lo/2) hband hlow hhigh
  rw [show lo-lo/2 = lo/2 by ring] at hl
  refine ⟨Q.squareFunction_moment_of_supported grid hb hwidth' hB hQ hp,?_⟩
  exact hmoment N κ ι Q B hB hQ hl hh grid hb hwidth' p hp

end LipschitzHilbert.LinePacketFamily

end

end OAI
