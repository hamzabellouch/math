import OAI.Geometry.SurfaceImmersion.Geometry.UniformActualAmplitudeC1
import OAI.Geometry.SurfaceImmersion.Geometry.UniformRemainderBound
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveTermC1Bounds

namespace OAI

/-! A uniform background C1 bound for every actual corrected primitive term.
The bound is chosen before the cycle count and before the finite-point map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance uniformTermFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformTermFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem uniform_corrected_term_C1 {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) {D : ℝ} (hD : 0 ≤ D) :
    ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
      ∀ Dw : ℝ, 0 ≤ Dw → ∃ E : ℝ, 0 ≤ E ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) → A.WeightedBound 1 2 D G →
      ∀ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
      f.phase = d.perturbedPhases ell →
      f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) →
      ∀ a, A.TensorWeightedBound 1 1 E (f.term a) := by
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hamp⟩ := d.uniform_actual_amplitude_C1 hF r href
  obtain ⟨Du,hDu,hu⟩ := A.uniform_remainder_C1_bound d.B g r hD
  obtain ⟨V,hV,hv⟩ := d.perturbed_phase_C1_bound
  refine ⟨min pt 1,wt,mt,lt_min hpt zero_lt_one,hwt,hmt,?_⟩
  intro Dw hDw
  obtain ⟨R,hR,hampBound⟩ := hamp Dw Du hDw hDu
  let T := max R V
  have hT : 0 ≤ T := (zero_le_one.trans hR).trans (le_max_left _ _)
  obtain ⟨E,hE,hterm⟩ := d.B.primitive_term_background_C1_bound A hT
  refine ⟨E,hE,?_⟩
  intro ell psi hell hpsi hs hclose hbpsi G hG hnear hGbound f hfphase hfamp a
  have hampa := hampBound ell psi (fun i j => (hell i j).trans_le (min_le_left _ _))
    hpsi hs hclose hbpsi G hG hnear (hu G hG hGbound)
  apply hterm (f.amplitude a) (f.phase a) (f.smoothAmplitude a) (f.smoothPhase a)
  · intro i p hp
    rw [hfamp]
    have h := hampa i a p hp
    exact ⟨h.1.trans (le_max_left _ _),h.2.trans (le_max_left _ _)⟩
  · intro i y hy
    obtain ⟨p,hp,rfl⟩ := hy
    rw [hfphase]
    have h := hv ell (fun i j => (hell i j).le.trans (min_le_right _ _)) i a p hp
    exact ⟨h.1.trans (le_max_right _ _),h.2.trans (le_max_right _ _)⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
