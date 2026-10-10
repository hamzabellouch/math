import OAI.Probability.PosteriorReplicas.Information.ObservationCorrelation
import OAI.Probability.PosteriorReplicas.Information.ReplicaLoss

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma finiteEntropy_nonneg {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (q : Measure W) [IsProbabilityMeasure q] : 0 ≤ finiteEntropy q := by
  simpa only [finiteEntropy, neg_mul, mul_neg] using finite_crossEntropy_nonneg q q

lemma information_of_correlation_loss {t : ℕ} (ht : 0<t) {I B D : ℝ≥0∞} {H C : ℝ}
    (hD : D ≠ ∞) (hH : 0 ≤ H) (hinfo : (t:ℝ≥0∞)*I+B ≤ D+ENNReal.ofReal H)
    (hloss : D.toReal ≤ B.toReal+C) : I ≤ ENNReal.ofReal ((H+C)/(t:ℝ)) := by
  have hR : D+ENNReal.ofReal H ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hD,ENNReal.ofReal_ne_top⟩
  have hB : B ≠ ∞ := ne_top_of_le_ne_top hR ((le_add_left le_rfl).trans hinfo)
  have hM : (t:ℝ≥0∞)*I ≠ ∞ := ne_top_of_le_ne_top hR ((le_add_right le_rfl).trans hinfo)
  have htn : (t:ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have hI : I ≠ ∞ := by intro h; simp [h,htn] at hM
  have hr := ENNReal.toReal_mono hR hinfo
  rw [ENNReal.toReal_add hM hB,ENNReal.toReal_add hD ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hH] at hr
  have htr : 0 < (t:ℝ) := by exact_mod_cast ht
  have hi : I.toReal ≤ (H+C)/(t:ℝ) := by
    apply (le_div_iff₀ htr).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal hI]
  exact ENNReal.ofReal_le_ofReal hi

lemma gaussian_replica_information_cost {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    conditionalInformation (sideLaw ℓ (signalMessageLaw ((sphereLaw d).withDensity f) κ)) ≤
      ENNReal.ofReal ((messageEntropy (signalMessageLaw ((sphereLaw d).withDensity f) κ)+
        comparisonCost d ℓ k m J)/((m+1:ℕ):ℝ)) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hd' : k+m+2 ≤ d := by omega
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd' hk hm .spherical hf hLt hfL
  let Q := posteriorMessageLaw (m := m) .spherical hf κ
  let q := signalMessageLaw ((sphereLaw d).withDensity f) κ
  have hinfo := random_replica_measure_information (gaussianRows d ℓ) Q q
    (fun i => posteriorMessageLaw_coordinate (by omega) (by omega) .spherical hf hLt hfL κ i)
    (g := fun z => labels z.1 z.2) measurable_labels
  have hQ : Q.snd = q.snd := posteriorMessageLaw_message (by omega) (by omega) .spherical hf hLt hfL κ
  rw [hQ] at hinfo
  have hTC := replica_tuple_klDiv_le hd' hk hm hf hLt hfL κ
  have hinfo' := hinfo.trans (add_le_add hTC le_rfl)
  have hloss := replica_lifted_loss hd hk hm hkm hf hLt hfL J hcut
  rw [replica_observe_klDiv_eq hd' hk hm hf hLt hfL κ] at hloss
  exact information_of_correlation_loss (by omega : 0 < m + 1)
    (replica_klDiv_ne_top hd hk hm hf hLt hfL) (finiteEntropy_nonneg q.snd) hinfo' hloss

end PosteriorReplicas
end

end OAI
