import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionJet
import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionSingularDirection

namespace OAI

/-! An unconditional generic map to three-space with finitely many
singularities, expressed using the actual derivative-direction map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_regular_crosscap_map :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          φ =ᶠ[𝓝 (chart q p)] f ∘ (chart q).symm ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨F,hF,hI⟩ := exists_smooth_euclidean_four_immersion (M := M)
  let e : ProjectionTarget 4 ≃L[ℝ] ProjectionTarget 3 × ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨he,heI⟩ := smooth_immersion_postcompose e.toContinuousLinearMap e.injective hF hI
  obtain ⟨a,hreg,hg,hfin⟩ := A.exists_finite_singular_projection he heI
  refine ⟨graphProjection a ∘ (e ∘ F),hg,hfin,?_⟩
  intro p hp
  obtain ⟨i,b,t,Φ,hi,_ht,hΦ,heq,hzero,hbij⟩ :=
    A.singular_projection_crosscap_jet he heI a hreg p hp
  refine ⟨(i : M),graphProjection a ∘ Φ,b,t,A.weightCore_source i hi,
    (graphProjection a).contDiff.comp hΦ,?_,?_,?_⟩
  · filter_upwards [heq] with x hx
    exact congrArg (graphProjection a) hx
  · rw [surfaceDirection_projected hΦ]
    exact hzero
  · rw [surfaceDirection_projected_fderiv hΦ]
    exact hbij

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
