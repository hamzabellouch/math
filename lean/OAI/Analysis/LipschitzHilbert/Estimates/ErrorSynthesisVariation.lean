import OAI.Analysis.LipschitzHilbert.Phase.AngularErrorMoments
import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative

namespace OAI

/-! The actual error synthesis variation is bounded by its positive
coefficient envelope, then by the constructed error moments. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem norm_diagonalSynthesis_le {Ω ι κ : Type*} [Fintype ι] [Fintype κ]
    (wave : ι → κ → Ω → ℂ) (c : ι → EuclideanSpace ℂ κ) (E : ι → ℝ)
    (z : Ω) {D : ℝ} (hD : 0 ≤ D) (hE : ∀ i, 0 ≤ E i)
    (hw : ∀ i k, ‖wave i k z‖ ≤ D * E i) :
    ‖diagonalSynthesis wave c z‖ ≤ D * ∑ i, ‖c i‖ * E i := by
  have heq : diagonalSynthesis wave c z = ∑ i, WithLp.toLp 2 (fun k => c i k * wave i k z) := by
    ext k
    simp only [diagonalSynthesis, WithLp.ofLp_sum, Finset.sum_apply]
  rw [heq, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  convert diagonal_packet_norm (c i) (fun k => wave i k z) (mul_nonneg hD (hE i)) (hw i) using 1
  ring

namespace AngularErrorFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def synthesisVariation (P : AngularErrorFamily N κ ι)
    (synth : ∀ j, ι j → κ → ℝ × ℝ → ℂ) (y x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => diagonalSynthesis (synth j) (P.coefficient j) (x,y))) N

theorem synthesisVariation_le (P : AngularErrorFamily N κ ι)
    (synth : ∀ j, ι j → κ → ℝ × ℝ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ j i k z, ‖synth j i k z‖ ≤ D *
      tileEnvelope (P.baseX+P.length j*(P.site j i).1) (P.baseZ+P.width*(P.site j i).2)
        (P.length j) P.width 6 z) (y x : ℝ) :
    P.synthesisVariation synth y x ≤ D * P.error y x := by
  apply (cubicVariation_packetPartialSum_le _).trans
  change (∑ j, ‖diagonalSynthesis (synth j) (P.coefficient j) (x,y)‖) ≤ D * ∑ j, P.scaleError j y x
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => norm_diagonalSynthesis_le _ _ _ _ hD
    (fun i => tileEnvelope_nonneg _ _ _ _ _ _) (fun i k => hs j i k (x,y)))

theorem synthesisVariation_moment (P : AngularErrorFamily N κ ι)
    (synth : ∀ j, ι j → κ → ℝ × ℝ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ j i k z, ‖synth j i k z‖ ≤ D *
      tileEnvelope (P.baseX+P.length j*(P.site j i).1) (P.baseZ+P.width*(P.site j i).2)
        (P.length j) P.width 6 z) (y : ℝ) (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hwidth : P.topLength ≤ grid.width) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.synthesisVariation synth y x))^p ∂grid.lineMeasure) ≤
      (ENNReal.ofReal D)^p * ((2:ℝ≥0∞)^p *
        (7 * ENNReal.ofReal ((p * (((grid.branching:ℝ)+2) *
          (2*(P.sources y).meanConstant+(P.sources y).oscillationConstant+1)) / Real.log (3/2))^p) +
          (ENNReal.ofReal (P.sources y).meanConstant)^p) * grid.lineMeasure Set.univ) := by
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal D)^p * (ENNReal.ofReal (P.error y x))^p ∂grid.lineMeasure := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp, ← ENNReal.ofReal_mul hD]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (P.synthesisVariation_le synth hD hs y x)) hp
    _ = (ENNReal.ofReal D)^p * ∫⁻ x, (ENNReal.ofReal (P.error y x))^p ∂grid.lineMeasure :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ _ := mul_le_mul_right (P.error_moment y grid hb hwidth hp) _

end AngularErrorFamily
end LipschitzHilbert

end

end OAI
