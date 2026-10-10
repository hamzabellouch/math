import OAI.Analysis.CoulombTransport.LocalBranchMeasure
import OAI.Analysis.CoulombTransport.SmoothPushforward

namespace OAI

/-! Square-density transport through globally measurable extensions of local branches. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem356

/-- A square density is concentrated on every measurable set containing the amplitude's support. -/
theorem squareDensity_ae_mem_of_tsupport_subset
    (g : E3 → ℝ) {U : Set E3} (hU : MeasurableSet U) (hg : tsupport g ⊆ U) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ U := by
  apply ae_iff.mpr
  change densityMeasure (fun x => g x ^ 2) Uᶜ = 0
  rw [densityMeasure, withDensity_apply _ hU.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hU.compl] with x hx
  have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hg ht))
  simp [hgx]

/-- Extending a local branch by a fixed value outside its source does not affect
its transport of a square density supported strictly inside that source. -/
theorem map_extendedBranch_squareDensity
    (e : OpenPartialHomeomorph E3 E3) (z : E3) (g : E3 → ℝ)
    (hg : tsupport g ⊆ e.source) :
    Measure.map (LocalBranchMeasure.extendedBranch e z)
        (densityMeasure (fun x => g x ^ 2)) =
      Measure.map e (densityMeasure (fun x => g x ^ 2)) :=
  LocalBranchMeasure.map_extendedBranch e z _
    (squareDensity_ae_mem_of_tsupport_subset g e.open_source.measurableSet hg)

/-- The exact inverse-Jacobian pushforward formula for a globally Borel branch. -/
theorem map_squareDensity_extendedBranch
    (e : OpenPartialHomeomorph E3 E3) (z : E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map (LocalBranchMeasure.extendedBranch e z)
        (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun t => Real.sqrt |(D t).det|) y ^ 2) := by
  rw [map_extendedBranch_squareDensity e z g hgs]
  exact map_squareDensity_localHomeomorph e g hgs D hD

end Problem356

end

end OAI
