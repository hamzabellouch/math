import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarWeightedPDE
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatJetContinuity

namespace OAI

/-! Continuous extension of the actual weighted continuation to the
closed spin interval, uniformly with respect to the slab variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma continuousOn_zero_spin_extension (f : ℝ × ℝ → ℝ)
    (hc : ∀ p : ℝ × ℝ, |p.2| < 1 → ContinuousAt f p)
    (hb : ∀ p : ℝ × ℝ, |p.2| = 1 →
      Tendsto f (𝓝[{q : ℝ × ℝ | |q.2| < 1}] p) (𝓝 0)) :
    ContinuousOn (fun p : ℝ × ℝ => if |p.2| < 1 then f p else 0)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := {q | |q.2| < 1}
  let g := fun p : ℝ × ℝ => if |p.2| < 1 then f p else 0
  intro p hp
  change ContinuousWithinAt g _ p
  by_cases hi : |p.2| < 1
  · have he : g =ᶠ[𝓝 p] f := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hi] with q hq
      exact ite_eq_left hq
    exact ((hc p hi).congr_of_eventuallyEq he).continuousWithinAt
  · have he : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hi)
    have hg : g p = 0 := ite_eq_right hi
    have hin : Tendsto g (𝓝[S] p) (𝓝 (0 : ℝ)) := by
      apply (hb p he).congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (ite_eq_left hq).symm
    have hout : Tendsto g (𝓝[Sᶜ] p) (𝓝 (0 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (ite_eq_right hq).symm
    have hall : Tendsto g (𝓝[S ∪ Sᶜ] p) (𝓝 (0 : ℝ)) := by
      rw [nhdsWithin_union, tendsto_sup]
      exact ⟨hin, hout⟩
    have hall' : Tendsto g (𝓝 p) (𝓝 (0 : ℝ)) := by simpa only [union_compl_self, nhdsWithin_univ] using hall
    rw [← hg] at hall'
    exact hall'.mono_left nhdsWithin_le_nhds

def closedMagneticSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabWeighted L hL A ζ p.1 p.2 else 0

lemma magneticScalarSlabWeighted_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) {p : ℝ × ℝ} (hp : |p.2| < 1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ q.1 q.2) p := by
  let P := magneticLogCoshMeanFourJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  let q := (p.1, magneticScalarSlabBias L ζ p.1 p.2)
  have hq : magneticHeatCurvature P.toMagneticContinuationJet F ζ q ≠ 0 := by
    have hh := (magneticScalarSlab_curvature_pos L hL hζ p.1 q.2).ne'
    simpa only [magneticHeatCurvature_eq _ F hF.1, P, magneticLogCoshMeanFourJet_eq, q, F] using hh
  have hcont : ContinuousAt (magneticHeatWeighted P A F ζ) q := by
    exact (continuous_magneticHeatSecond P.toMagneticContinuationJet A F hcF hF.2 ζ).continuousAt.sub
      (((continuous_magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet
        F hcF hF.2 ζ).continuousAt.mul
          (continuous_magneticHeatSecond P.toMagneticContinuationJet P F hcF hF.2 ζ).continuousAt).div
            (continuous_magneticHeatCurvature P.toMagneticContinuationJet F hcF hF.2 ζ).continuousAt hq)
  have hb := magneticScalarSlabBias_continuousAt_joint L hL (v := p.1) hζ hp
  have hh := hcont.comp' (f := fun r : ℝ × ℝ =>
    (r.1, magneticScalarSlabBias L ζ r.1 r.2)) (x := p) (continuousAt_fst.prodMk hb)
  simpa only [← magneticScalarSlabWeighted_eq_heat, P, F, q] using hh

theorem continuousOn_closedMagneticSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ContinuousOn (closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  apply continuousOn_zero_spin_extension
  · exact fun p hp => magneticScalarSlabWeighted_continuousAt L hL A hζ hp
  · intro p hp
    have he : p.2 = -1 ∨ p.2 = 1 := by
      rcases le_total 0 p.2 with h | h
      · exact Or.inr (by rwa [abs_of_nonneg h] at hp)
      · exact Or.inl (by rw [abs_of_nonpos h] at hp; linarith)
    apply magneticScalarSlabWeighted_tendsto_endpoint L hL hL1 A.toMagneticContinuationJet hA hζ hζ1 he
    · exact self_mem_nhdsWithin
    · exact continuous_snd.continuousAt.mono_left nhdsWithin_le_nhds

end InvariantIsing

end

end OAI
