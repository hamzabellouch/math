import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNuclearBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.Average

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma shifted_reaction_convex {k : ℝ} (hk : 0 ≤ k) (c : ℝ) :
    ConvexOn ℝ univ (fun t => reaction k (c+t)) := by
  simpa only [preimage_univ,Function.comp_def] using (reaction_convex hk).translate_right c

theorem weak_nuclear_average {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Set TFSpace} (Z : ℝ)
    {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k) (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw : ∀ᵐ sample ∂P, WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u sample x)
      (fun x => g sample x+χ x*reaction k (nuclearField Z x+u sample x))) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+∫ sample, u sample x ∂P)
      (fun x => (∫ sample, g sample x ∂P)+χ x*reaction k (nuclearField Z x+∫ sample, u sample x ∂P)) := by
  rw [weakNuclearLower_add_iff Z (average_locallyIntegrable hu hub)]
  simp_rw [weighted_clipped_reaction Z R hzero]
  apply weak_spatial_average hu hub huc hg hgb hχ hχb hχn
    (F := fun x t => reaction k (clippedNuclearField Z R x+t))
    ((reaction_continuous k).comp (((clippedNuclearField_continuous Z hR).comp continuous_fst).add continuous_snd))
    (fun x => shifted_reaction_convex hk _)
  filter_upwards [hw,huc] with sample hw hc
  have hw' := (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hw
  simpa only [weighted_clipped_reaction Z R hzero] using hw'

end CoulombBarrier

end

end OAI
