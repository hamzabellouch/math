import OAI.Geometry.SurfaceImmersion.Primitive.ExteriorClosureProfiles
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasProjectionStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorApproximation

namespace OAI

/-! The retained slow baseline and C2 correction control the actual
normalized exterior normal, uniformly over every atlas chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_projected_normal_close_closure {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O,
      A.projectedNormalField W n p ≠ 0 ∧ ‖A.unitProjectedNormalField W n p-n p‖ < ε := by
  classical
  obtain ⟨δ,hδ,hnear⟩ := A.compact_atlas_projection_stability hF hn hunit hN hD hε
  choose D hD0 hbound using fun i => A.exterior_read_C2_bound_closure i
  obtain ⟨ρ,hρ,_,hle⟩ := finite_positive_threshold (fun i => δ/(D i+1))
    (fun i => div_pos hδ (by have := hD0 i; positivity))
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hpO
  apply hnear W p
  intro i hi v hv
  have hp := subset_tsupport (A.weight i) hi
  have hd := hbound i F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp 1 (by omega)
  rw [norm_iteratedFDeriv_one] at hd
  have hs : D i*(b+c) < δ := by
    have ht := (lt_div_iff₀ (by have := hD0 i; positivity : 0 < D i+1)).mp
      (hbc.trans_le (hle i))
    nlinarith
  have hnV : ‖v‖ ≤ 1 := by
    rcases hv with rfl | hv
    · simp [dx]
    · have hv' : v = dy := by simpa only [mem_singleton_iff] using hv
      subst v
      simp [dy]
  have hre : spaceCoordinates ∘ A.vectorPlaneRead i (W-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i W)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact map_sub spaceCoordinates _ _
  rw [hre,fderiv_sub
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hW).differentiable (by simp) _))
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _))] at hd
  change ‖((fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i W) _)-
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _)) v‖ < δ
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_left hnV (norm_nonneg _)).trans (by simpa only [mul_one] using hd))).trans_lt hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
