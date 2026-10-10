import OAI.Analysis.LipschitzHilbert.Estimates.TopWeakTwo

namespace OAI

/-! Restricted testing gives the top-count bound on the localization
strip, without extending the short-side geometry beyond that strip. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem top_count_weak_two_on_set {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (K R D A : ℝ) (hK : 0 < K) (hKR : K ≤ R) (hD : 4 ≤ D) (hA : 0 ≤ A)
    (htest : ∀ Q : Set (ℝ × ℝ), MeasurableSet Q →
      (volume.prod volume) Q ≠ ∞ → Q ⊆ S → ∀ n : ℕ,
      (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation (R*2^n))) ≤
        ENNReal.ofReal (A*(R*2^n)^3*Real.sqrt ((volume.prod volume).real Q)))
    (t : ℝ) (ht : 0 < t) :
    (volume.prod volume) (S ∩ {z | t < ∑ i, (T i).weight K D z}) ≤
      ENNReal.ofReal ((2*4^D*A*R^3)^2/t^2) := by
  classical
  let μ := (volume.prod volume).restrict S
  have hm : Measurable (fun z => ∑ i, (T i).weight K D z) :=
    Finset.measurable_sum _ (fun i _ => ((T i).weight_continuous K D hK).measurable)
  have hi : Integrable (fun z => ∑ i, (T i).weight K D z) μ :=
    (integrable_finsetSum _ (fun i _ => (T i).weight_integrable hK (by linarith))).mono_measure
      Measure.restrict_le_self
  have hw := weak_two_of_testing μ _ hm hi (2*4^D*A*R^3)
    (by have : 0 < R := hK.trans_le hKR; positivity) (by
      intro Q hQ hQfin
      have hQfin' : (volume.prod volume) (Q ∩ S) ≠ ∞ := by
        simpa only [μ, Measure.restrict_apply hQ] using hQfin
      have hQS : μ.real Q = (volume.prod volume).real (Q ∩ S) := by
        simp only [Measure.real, μ, Measure.restrict_apply hQ]
      have hd := top_lintegral_of_dilated_testing (μ.restrict Q) T K R D
        (A*Real.sqrt (μ.real Q)) hK hKR hD (by positivity) (by
          intro n
          have hp := htest (Q ∩ S) (hQ.inter hS) hQfin' inter_subset_right n
          simpa only [μ, Measure.restrict_apply ((T _).measurableSet_radialDilation _),
            Measure.restrict_apply (((T _).measurableSet_radialDilation _).inter hQ),
            Measure.restrict_apply (hQ.inter ((T _).measurableSet_radialDilation _)),
            hQS, inter_assoc, inter_comm, inter_left_comm, mul_assoc, mul_comm, mul_left_comm]
            using hp)
      convert hd using 1
      congr 1
      ring) t ht
  simpa only [μ, Measure.restrict_apply (measurableSet_lt measurable_const hm), inter_comm]
    using hw

end LipschitzHilbert

end

end OAI
