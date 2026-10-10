import OAI.Geometry.Immersion.ClosedSurface.AtlasWeights
import OAI.Geometry.Immersion.ClosedSurface.PhaseDifferentials

namespace OAI

/-! A uniform positive pure-phase margin after passage to another chart
of the fixed finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {ι : Type*} [Fintype ι]

theorem finite_atlas_pure_margin (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ ∀ (h : ℝ) (s : ι → Finset Index)
      (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base)
      (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ a q, atlasActive p ψ s h a q →
        atlasGram G (p a.1) q ≠ 0 ∧ atlasSecondTensor G (p a.1) q ≠ 0 ∧
        ε*‖atlasSecondTensor G (p a.1) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (p a.1) q) (-(ξ a).2,(ξ a).1)‖) →
      ∀ a j q, atlasActive p ψ s h a q → q ∈ tsupport (ψ j) →
        e*‖atlasSecondTensor G (p j) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (p j) q)
            (-(atlasPhaseCovector (p a.1) (p j) (ξ a) q).2,
              (atlasPhaseCovector (p a.1) (p j) (ξ a) q).1)‖ := by
  obtain ⟨d,L,hd,hL,hbound⟩ := finite_atlas_transition_bounds p ψ hsource hcompact
  let e := d^2*ε/(4*L^2)
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hd) hε)
    (mul_pos (by norm_num) (sq_pos_of_pos hL))
  refine ⟨e,he,?_⟩
  intro h s ξ G hG hlocal a j q ha hq
  have hqa : q ∈ tsupport (ψ a.1) :=
    refinedCutoff_tsupport_outer (p a.1) (ψ a.1) (s a.1) h a.2.1 ha.2
  have hap : q ∈ (coordinateChart (p a.1)).source := by
    rw [coordinateChart_source]
    exact hsource a.1 hqa
  have hjp : q ∈ (coordinateChart (p j)).source := by
    rw [coordinateChart_source]
    exact hsource j hq
  have hc := hbound j a.1 (coordinateChart (p j) q) ⟨q,⟨hq,hqa⟩,rfl⟩
  have hl := hlocal a q ha
  exact (actual_phase_margin_at hG (p a.1) (p j) hjp hap (ξ a)
    hd hL hε hl.1 hc.1 hc.2 hl.2.1 hl.2.2).2.1

lemma atlasPhaseCovector_smul (q p : M) (ξ : SmallModes.Base) (w : ℝ) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    atlasPhaseCovector q p (w • ξ) a = w • atlasPhaseCovector q p ξ a := by
  have he : atlasPhase q (w • ξ) = w • atlasPhase q ξ := by
    funext z
    simp only [atlasPhase,Function.comp_apply,phaseLinear_apply,Prod.smul_fst,
      Prod.smul_snd,smul_eq_mul,Pi.smul_apply]
    ring
  unfold atlasPhaseCovector
  rw [he]
  change phaseDerivative (w • (atlasPhase q ξ ∘ (coordinateChart p).symm))
    (coordinateChart p a) = _
  exact phaseDerivative_const_smul (atlasPhase_in_chart_differentiable q p ξ hap haq) w

end ClosedSurfaceR4

end

end OAI
