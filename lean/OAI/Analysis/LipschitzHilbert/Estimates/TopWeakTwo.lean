import OAI.Analysis.LipschitzHilbert.Estimates.TopDilatedTesting
import OAI.Analysis.LipschitzHilbert.Estimates.TestingWeakTwo

namespace OAI

/-! The actual top count satisfies weak L2 once the geometric dilation
packing bounds are available. This is the final analytic part of the
popular-top counting argument, with no dependence on the number of tops. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem top_count_weak_two_of_dilations {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (K R D A : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 4 ≤ D) (hA : 0 ≤ A)
    (htest : ∀ Q : Set (ℝ × ℝ), MeasurableSet Q →
      (volume.prod volume) Q ≠ ∞ → ∀ n : ℕ,
      (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation (R*2^n))) ≤
        ENNReal.ofReal (A*(R*2^n)^3*Real.sqrt ((volume.prod volume).real Q)))
    (t : ℝ) (ht : 0 < t) :
    (volume.prod volume) {z | t < ∑ i, (T i).weight K D z} ≤
      ENNReal.ofReal ((2*4^D*A*R^3)^2/t^2) := by
  classical
  have hm : Measurable (fun z => ∑ i, (T i).weight K D z) :=
    Finset.measurable_sum _ (fun i _ => ((T i).weight_continuous K D hK).measurable)
  have hi : Integrable (fun z => ∑ i, (T i).weight K D z) (volume.prod volume) :=
    integrable_finsetSum _ (fun i _ => (T i).weight_integrable hK (by linarith))
  apply weak_two_of_testing (volume.prod volume) _ hm hi (2*4^D*A*R^3)
    (by have : 0 < R := hK.trans_le hKR; positivity) _ t ht
  intro Q hQ hQfin
  have hd := top_lintegral_of_dilated_testing ((volume.prod volume).restrict Q) T K R D
    (A*Real.sqrt ((volume.prod volume).real Q)) hK hKR hD (by positivity) (by
      intro n
      simpa only [Measure.restrict_apply ((T _).measurableSet_radialDilation _),
        inter_comm, mul_assoc, mul_left_comm, mul_comm] using htest Q hQ hQfin n)
  convert hd using 1
  congr 1
  ring

end LipschitzHilbert

end

end OAI
