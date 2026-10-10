import OAI.Probability.GammaPassage.MeanNorm
import OAI.Probability.GammaPassage.MeanSwap
import OAI.Probability.GammaPassage.AnalyticCore

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

lemma rationalMean_swap (m : Vertex → ℝ) (hm : ∀ z, m z.swap=m z)
    (q : ℚ × ℚ) : rationalMean m q.swap = rationalMean m q := by
  have hn : rationalNumerator q.swap = (rationalNumerator q).swap := rfl
  have hd : rationalDenominator q.swap = rationalDenominator q := by
    simp only [rationalDenominator, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm]
  simp only [rationalMean, hn, hd, hm]

lemma realMeanExtension_swap {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hs : ∀ q, f q.swap=f q) (v : ℝ × ℝ) :
    realMeanExtension f v.swap = realMeanExtension f v := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property rationalPairCast_dense
    (p := fun v : ℝ × ℝ => realMeanExtension f v.swap=realMeanExtension f v) ?_ ?_ v
  · exact isClosed_eq (hc.comp (continuous_snd.prodMk continuous_fst)) hc
  · intro q
    have he : (rationalPairCast q).swap = rationalPairCast q.swap := rfl
    rw [he, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hs q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_swap (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (v : ℝ × ℝ) :
    gammaMeanPairSeminorm h hs hr v.swap = gammaMeanPairSeminorm h hs hr v := by
  change realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v.swap =
    realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_swap
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  exact rationalMean_swap _ (h.directionalMeanConstant_coordinateSwap hs hr) q

/-- Derived from actual expectation-limit symmetry through rational density. -/
theorem gammaMeanNorm_swap (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (v : Plane) :
    gammaMeanNorm h hs hr (Analytic.swapPlane v) = gammaMeanNorm h hs hr v := by
  change gammaMeanPairSeminorm h hs hr
    ((Analytic.swapPlane v) 0, (Analytic.swapPlane v) 1) =
      gammaMeanPairSeminorm h hs hr (v 0,v 1)
  rw [Analytic.swapPlane_zero, Analytic.swapPlane_one]
  exact gammaMeanPairSeminorm_swap h hs hr (v 0,v 1)

end GammaFPP

end OAI
