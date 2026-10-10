import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedEnvelopeKernel

namespace OAI

/-! The reciprocal top weight has an absolute square-integral proportional
to the top area. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem topReciprocalWeight_energy (a b L W : ℝ) (hL : 0<L) (hW : 0<W) :
    MemLp (topReciprocalWeight a b L W) 2 (volume.prod volume) ∧
      (∫ z, (topReciprocalWeight a b L W z)^2 ∂volume.prod volume)≤Real.pi^2*L*W := by
  let D := topReciprocalWeight a b L W
  have hm : Measurable D := topReciprocalWeight_measurable a b L W
  have hi : Integrable D (volume.prod volume) :=
    tileEnvelope_integrable a b L W (by decide : 1≤1) hL hW
  have hb (z : ℝ×ℝ) : ‖D z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (topReciprocalWeight_nonneg a b L W z)]
    exact topReciprocalWeight_le_one a b L W z
  have hs : Integrable (fun z => (D z)^2) (volume.prod volume) := by
    simpa only [pow_two] using hi.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hs,?_⟩
  calc
    _ ≤ ∫ z, D z ∂volume.prod volume := integral_mono hs hi (fun z => by
      have h0 := topReciprocalWeight_nonneg a b L W z
      have h1 := topReciprocalWeight_le_one a b L W z
      change (D z)^2≤D z
      nlinarith)
    _ = (∫ x, lineEnvelope a L 1 x)*(∫ y, lineEnvelope b W 1 y) :=
      integral_prod_mul _ _
    _ = Real.pi^2*L*W := by
      rw [integral_lineEnvelope_one a L hL,integral_lineEnvelope_one b W hW]
      ring

end LipschitzHilbert

end

end OAI
