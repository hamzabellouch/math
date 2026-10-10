import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformationClipping
import OAI.NumberTheory.PrimePackets.FutureConditionalEntropy

namespace OAI

/-! # Whole-future conditional information is bounded by metric entropy

Finite present clips have their own, smaller future sigma algebra.
Conditioning on the full countable future and further transverse data
only decreases their entropy. Passing to the proved clipping limit gives
the bound without a finite Shannon entropy assumption on the countable
observation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*}

lemma clipped_future_sigma_le (T : Y → Y) (Q : Y → ℕ)
    (m : MeasurableSpace Y)
    (hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ m)
    (N : ℕ) : (⨆ k, observationSigma (futureName T (heightClip Q N) k)) ≤ m := by
  let : MeasurableSpace Y := m
  have hcoord (k : ℕ) : Measurable (fun y => Q (T^[k+1] y)) :=
    (comap_measurable _).mono ((le_iSup _ k).trans hfuture) le_rfl
  apply iSup_le
  intro k
  apply observationSigma_le
  intro w
  have hName : Measurable (futureName T (heightClip Q N) k) := by
    apply measurable_pi_iff.mpr
    intro i
    have heq : (fun y => futureName T (heightClip Q N) k y i) =
        heightClip (fun y => Q (T^[i.val+1] y)) N := by
      funext y
      apply Fin.ext
      simp only [futureName, orbitName, heightClip, Function.iterate_succ_apply]
    rw [heq]
    exact heightClip_measurable (hcoord i.val) N
  exact hName (measurableSet_singleton w)

theorem conditionalInformation_integral_le_metricEntropy
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
    (hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ m)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
    (hint : Integrable (conditionalInformation μ Q m) μ) :
    ENNReal.ofReal (∫ y, conditionalInformation μ Q m y ∂μ) ≤ measureEntropy μ T := by
  have hclip := conditionalSigmaEntropy_heightClip_tendsto m μ Q hQ hm hpos hint
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hclip)
  apply Filter.Eventually.of_forall
  intro N
  have hP := heightClip_measurable hQ N
  have hle : conditionalSigmaEntropy μ (heightClip Q N) m ≤
      observationEntropyRate μ T (heightClip Q N) := by
    rw [observationEntropyRate_eq_futureConditional μ hT _
      (fun a => hP (measurableSet_singleton a))]
    exact conditionalSigmaEntropy_antitone μ _
      (fun a => hP (measurableSet_singleton a))
      (clipped_future_sigma_le T Q m hfuture N) hm
  apply (ENNReal.ofReal_le_ofReal hle).trans
  unfold measureEntropy
  exact le_iSup_of_le (N+1) (le_iSup_of_le (heightClip Q N)
    (le_iSup_of_le (fun a => hP (measurableSet_singleton a)) le_rfl))

end DukePrimeDegree

end

end OAI
