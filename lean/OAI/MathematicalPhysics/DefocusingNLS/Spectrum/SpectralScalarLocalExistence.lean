import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFiniteExistence
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! Scalar comparison solutions need only local coefficient continuity on the
interval under consideration. The coefficient is extended by clamping. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_local_exists (a b : ℝ) (hab : a≤ b)
    (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b)) (x : ℂ × ℂ) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧ q a=x ∧
      ∀ r ∈ Icc a b, HasDerivAt q (spectralScalarField (V r) (q r)) r := by
  let W := fun r : ℝ => V (projIcc a b hab r)
  have hW : Continuous W := hV.domRestrict.comp continuous_projIcc
  have hWeq (r : ℝ) (hr : r ∈ Icc a b) : W r=V r := by
    simp only [W,projIcc_of_mem _ hr]
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  have hbound (r : ℝ) (hr : r ∈ Icc a b) : ‖W r‖≤ max B 0 := by
    rw [hWeq r hr]
    exact (hB r hr).trans (le_max_left _ _)
  obtain ⟨q,hq,hqa,hqd⟩ := spectralScalar_finite_exists a b (max B 0) hab
    (le_max_right _ _) W hW hbound x
  refine ⟨q,hq,hqa,?_⟩
  intro r hr
  simpa only [hWeq r hr] using hqd r hr

end DefocusingNLS

end OAI
