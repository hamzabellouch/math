import OAI.Analysis.Mahler.GlobalPlanarBound

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- The original primitive is strictly increasing on every entire actual
vertical section, including across its possible zero derivative at the origin. -/
theorem strictMonoOn_planarPrimitive_global {m : ℕ} (hm : 0 < m) {q : ℝ}
    (hq : q ∈ Ioo (-1 : ℝ) 1) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  have hv := verticalFiber_interval hq
  have hcont : ∀ a b : ℝ, a ∈ verticalFiber q → b ∈ verticalFiber q →
      ContinuousOn (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) (uIcc a b) := by
    intro a b ha hb s hs
    have hmem : s ∈ verticalFiber q := hv.2.1.uIcc_subset ha hb hs
    exact (continuousAt_planarDensity_vertical m hmem).continuousWithinAt
  intro a ha b hb hab
  have h0 : (0 : ℝ) ∈ verticalFiber q := hv.2.2
  have hia := (hcont 0 a h0 ha).intervalIntegrable (μ := volume)
  have hiab := (hcont a b ha hb).intervalIntegrable (μ := volume)
  have heq := intervalIntegral.integral_add_adjacent_intervals hia hiab
  have hpos : 0 < ∫ s in a..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
    apply intervalIntegral.integral_pos hab
    · simpa only [uIcc_of_le hab.le] using hcont a b ha hb
    · intro s _
      exact planarDensity_nonneg m _
    · by_cases ha0 : a = 0
      · refine ⟨b,⟨hab.le,le_rfl⟩,planarDensity_pos hm hb ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      · refine ⟨a,⟨le_rfl,hab.le⟩,planarDensity_pos hm ha ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        exact ha0 him
  change (∫ s in (0 : ℝ)..a, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) <
    ∫ s in (0 : ℝ)..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)
  linarith

end SymmetricMahler

end OAI
