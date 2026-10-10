import OAI.Geometry.IsometricImmersion.Pulses.OriginalPulseExclusion
import OAI.Geometry.IsometricImmersion.Obstructions.BoundedClassTopology

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.Model

theorem boundedHeightClass_isNowhereDense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    (M : ℕ) (q0 : ℚ) :
    IsNowhereDense (boundedHeightClass g0 kappa M q0) := by
  change interior (closure (boundedHeightClass g0 kappa M q0)) = ∅
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro etaStar hStar
  let O := interior (closure (boundedHeightClass g0 kappa M q0))
  have hO : IsOpen O := isOpen_interior
  have hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0) := interior_subset
  have hparameters := boundedHeightClass_closure_parameters (hOclosure hStar)
  have hgStar : SmoothPositiveOn (perturbedMetric g0 etaStar.val) V :=
    perturbedMetric_smoothPositiveOn hg0 etaStar.val etaStar.property.1
  obtain ⟨r,hr,_,hLr,hexclusion⟩ := exists_original_pulse_exclusion
    hg0 hgStar hV hSV M hkappa hparameters.1 hparameters.2.le hbackground
  obtain ⟨N,hN,happroximants⟩ := bounded_class_open_closure_pulse_family_at_radius
    hg0 hV hSV M q0 hO hStar hOclosure hr hLr
  obtain ⟨delta,hdelt,_,hnoheight⟩ := hexclusion N hN
  obtain ⟨tau,happroxTau,hnoheightTau⟩ := ((happroximants delta hdelt).and hnoheight).exists
  obtain ⟨eta,z,hclass,hcenter,haccuracy⟩ := happroxTau.2
  exact hnoheightTau eta z hclass hcenter haccuracy

end SmoothLocal.Perturbation

end

end OAI
