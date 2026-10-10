import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareSlabConvex
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatContinuity

namespace OAI

/-! The finite square continuation on the closed spin interval. Its two
endpoint values are one, and its time derivatives there vanish. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabContinuation_bounds (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    magneticScalarSlabContinuation L A ζ v s ∈ Icc (s ^ 2) 1 := by
  have hb := magneticScalarSlabContinuation_sandwich L hL A hA ζ v (magneticScalarSlabBias L ζ v s)
  have hr := magneticScalarSlabMean_bias L hL hζ hs v
  change (magneticScalarSlabJet L hL ζ v).value (magneticScalarSlabBias L ζ v s) = s at hr
  rw [hr] at hb
  rwa [magneticScalarSlabContinuation_eq_jet L hL A ζ v s]

lemma magneticScalarSlabContinuation_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) {p : ℝ × ℝ} (hp : |p.2| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarSlabContinuation L A ζ q.1 q.2) p := by
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have hc := (continuous_magneticHeatMean A F hcF hF.2 ζ).continuousAt
    (x := (p.1, magneticScalarSlabBias L ζ p.1 p.2))
  have hb := magneticScalarSlabBias_continuousAt_joint L hL (v := p.1) hζ hp
  exact hc.comp' (f := fun q : ℝ × ℝ => (q.1, magneticScalarSlabBias L ζ q.1 q.2))
    (x := p) (continuousAt_fst.prodMk hb)

def closedMagneticContinuation (L : List (ℝ × ℝ≥0))
    (A : MagneticContinuationJet) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuation L A ζ p.1 p.2 else 1

lemma closedMagneticContinuation_bounds (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (p : ℝ × ℝ) (hp : p.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L A ζ p ∈ Icc (p.2 ^ 2) 1 := by
  by_cases hs : |p.2| < 1
  · simpa only [closedMagneticContinuation, hs, ite_true] using
      magneticScalarSlabContinuation_bounds L hL A hA hζ hs p.1
  · have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [hp.1, hp.2]
    simpa only [closedMagneticContinuation, hs, ite_false, Set.mem_Icc, le_refl, and_true] using hsq

lemma continuousOn_closedMagneticContinuation (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ContinuousOn (closedMagneticContinuation L A ζ) (univ ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  by_cases hs : |p.2| < 1
  · have he : closedMagneticContinuation L A ζ =ᶠ[𝓝 p]
        (fun q : ℝ × ℝ => magneticScalarSlabContinuation L A ζ q.1 q.2) := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs] with q hq
      exact ite_eq_left hq
    exact ((magneticScalarSlabContinuation_continuousAt L hL A hζ hs).congr_of_eventuallyEq he).continuousWithinAt
  · have hps : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hs)
    have hps2 : p.2 ^ 2 = 1 := by nlinarith [sq_abs p.2]
    change Tendsto (closedMagneticContinuation L A ζ) (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 _)
    rw [show closedMagneticContinuation L A ζ p = 1 from ite_eq_right hs]
    have hlo : Tendsto (fun q : ℝ × ℝ => q.2 ^ 2)
        (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 (1 : ℝ)) := by
      have hc : ContinuousWithinAt (fun q : ℝ × ℝ => q.2 ^ 2)
          (univ ×ˢ Icc (-1 : ℝ) 1) p := by fun_prop
      simpa only [ContinuousWithinAt, hps2] using hc
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (closedMagneticContinuation_bounds L hL A hA hζ q hq.2).1
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (closedMagneticContinuation_bounds L hL A hA hζ q hq.2).2

end InvariantIsing

end

end OAI
