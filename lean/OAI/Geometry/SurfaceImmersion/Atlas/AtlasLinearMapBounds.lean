import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

namespace OAI

/-! Fixed linear coordinate changes preserve the actual atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V W : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_clm (p : M) (χ : M → ℝ) (L : V →L[ℝ] W) (F : M → V) :
    localize p χ (L ∘ F) = L ∘ localize p χ F := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize,hx,map_smul]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_clm (L : V →L[ℝ] W) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {s C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hb : A.WeightedBound s m C F) :
    A.WeightedBound s m (‖L‖*C) (L ∘ F) := by
  intro i
  rw [localize_clm]
  exact (hb i).linear uniqueDiffOn_univ hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn L

lemma weightedBound_add {F G : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (hG : ContMDiff planeModel 𝓘(ℝ,V) ∞ G)
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbF : A.WeightedBound s m C F) (hbG : A.WeightedBound s m D G) :
    A.WeightedBound s m (C+D) (F+G) := by
  intro i
  have he : localize (i : M) (A.weight i) (F+G) =
      localize (i : M) (A.weight i) F + localize (i : M) (A.weight i) G := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx,smul_add]
  change WeightedEstimates.WeightedBound univ s m (C+D) (localize (i : M) (A.weight i) (F+G))
  rw [he]
  exact (hbF i).add uniqueDiffOn_univ hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hG).contDiffOn (hbG i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
