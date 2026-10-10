import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialInteractionBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialRemainderBounds
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasJetProfiles
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetReadBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetSegmentEnlargement

namespace OAI

/-! Uniform nonlinear error bounds from the global norms used by the iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators Pointwise
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_nonlinear_profiles {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (R U V : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (hU : ∀ m, 0 ≤ U m) (hV : ∀ m, 0 ≤ V m) :
    ∃ E₁ E₂ : ℕ → ℝ, (∀ m, 0 ≤ E₁ m) ∧ (∀ m, 0 ≤ E₂ m) ∧
      ∀ (G X Y : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ X → ContMDiff planeModel spaceModel ∞ Y →
      ∀ (s : ℝ≥0) (τ ε δ : ℝ), 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ m, A.WeightedBound τ m (U m*(δ*τ)) X) →
      (∀ m, A.WeightedBound τ m (V m*δ^2) Y) →
      (∀ m, A.TensorWeightedBound τ m (E₁ m*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε G (X+Y)-A.atlasPolynomialQuadratic P ε G X)) ∧
      (∀ m, A.TensorWeightedBound τ m (E₂ m*(δ^3/τ))
        (A.atlasPolynomialRemainder P ε G (X+Y))) := by
  classical
  obtain ⟨K,B,hK,hB,hjet⟩ := A.atlas_jet_profiles Ω hΩ KΩ hΩK R hR
  choose D hD hd using fun i m => A.jetPlaneRead_bound i m
  let Cx := fun i m => 1+D i m*U m
  let Cy := fun i m => 1+D i m*V m
  let C := fun i m => Cx i m+Cy i m
  have hCx (i m) : 0 < Cx i m := by
    dsimp [Cx]
    linarith [mul_nonneg (hD i m) (hU m)]
  have hCy (i m) : 0 < Cy i m := by
    dsimp [Cy]
    linarith [mul_nonneg (hD i m) (hV m)]
  have hC (i m) : 0 < C i m := add_pos (hCx i m) (hCy i m)
  let K' := fun i => K i+Metric.closedBall (0 : LowJet) (C i 2)
  have hK' (i) : IsCompact (K' i) := (hK i).add (isCompact_closedBall _ _)
  choose E₁ hE₁ he₁ using fun m => A.atlas_polynomial_interaction_bound P hP Ω hΩ houter K hK m
    (fun i => B i (m+tensorOrder (P i)))
    (fun i => Cx i (m+tensorOrder (P i)+1)) (fun i => Cy i (m+tensorOrder (P i)+1))
    (fun i => hB i _) (fun i => hCx i _) (fun i => hCy i _)
  choose E₂ hE₂ he₂ using fun m => A.atlas_polynomial_remainder_bound P hP Ω hΩ houter K' hK' m
    (fun i => B i (m+tensorOrder (P i))+C i (m+tensorOrder (P i)+2))
    (fun i => C i (m+tensorOrder (P i)))
    (fun i => (hB i _).trans (le_add_of_nonneg_right (hC i _).le)) (fun i => hC i _)
  refine ⟨E₁,E₂,hE₁,hE₂,?_⟩
  intro G X Y hG hX hY s τ ε δ hτ hs hτs hs1 hε hε1 hδ hδτ hsmall hGb hXb hYb
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hδ2 : δ^2 ≤ δ*τ := by nlinarith
  obtain ⟨hmap,hbound⟩ := hjet G hG s hs hs1 hGb
  have hx (i m) : WeightedEstimates.WeightedBound univ τ m (Cx i m*δ*τ)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) := by
    have hh := hd i m X hX τ (U m*(δ*τ)) hτ hτ1 (mul_nonneg (hU m) (mul_nonneg hδ.le hτ.le)) (hXb m)
    apply hh.mono_const
    dsimp [Cx]
    nlinarith [mul_nonneg hδ.le hτ.le]
  have hy (i m) : WeightedEstimates.WeightedBound univ τ m (Cy i m*δ^2)
      (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    have hh := hd i m Y hY τ (V m*δ^2) hτ hτ1 (mul_nonneg (hV m) (sq_nonneg δ)) (hYb m)
    apply hh.mono_const
    dsimp [Cy]
    nlinarith [sq_nonneg δ]
  have hc (i m) : WeightedEstimates.WeightedBound univ τ m (C i m*δ*τ)
      (A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm) := by
    have hh := (hx i m).add uniqueDiffOn_univ hτ.le
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
      (((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff).contDiffOn) (hy i m)
    have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+(A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
      rw [A.jetChartMap_add]
      rfl
    rw [he]
    apply hh.mono_const
    have hh' := mul_le_mul_of_nonneg_left hδ2 (hCy i m).le
    dsimp only [C]
    nlinarith only [hh']
  have hc' (i m) : WeightedEstimates.WeightedBound (Ω i) τ m (C i m*δ*τ)
      (A.jetChartMap i (X+Y)) := by
    have hh := weightedBound_comp_isometry planeCoordinateIsometry
      ((A.jetChartMap_smooth i (hX.add hY)).comp planeCoordinateIsometry.symm.contDiff) (hc i m)
    have he : (A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =
        A.jetChartMap i (X+Y) := by
      funext x
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    rw [he] at hh
    exact hh.restrict_open (hΩ i)
  have hseg (i t) (ht : t ∈ Icc (0:ℝ) 1) : MapsTo
      (lowJet (fun x => A.jetChartMap i G x+t • A.jetChartMap i (X+Y) x)) (Ω i) (K' i) :=
    lowJet_segment_mem_add_closedBall (hΩ i) (A.jetChartMap_smooth i hG)
      (A.jetChartMap_smooth i (hX.add hY)) (hmap i) hτ hτ1 hδ.le hδτ (hC i 2).le (hc' i 2) ht
  have hsegb (i m t) (ht : t ∈ Icc (0:ℝ) 1) : WeightedEstimates.WeightedBound (Ω i) τ m
      (B i m+C i (m+2))
      (lowJet (fun x => A.jetChartMap i G x+t • A.jetChartMap i (X+Y) x)) := by
    have hh := lowJet_segment_bound (hΩ i) (A.jetChartMap_smooth i hG)
      (A.jetChartMap_smooth i (hX.add hY)) hτ hτ1 (mul_nonneg (mul_nonneg (hC i (m+2)).le hδ.le) hτ.le)
      ((hbound i m).shrink_scale hτ.le hτs) (hc' i (m+2)) ht
    apply hh.mono_const
    apply add_le_add le_rfl
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδτ hτ.le) (hC i (m+2)).le]
  constructor
  · intro m
    exact he₁ m G X Y hG hX hY τ ε δ hτ hτ1 hε hε1 hδ hδτ hsmall hmap
      (fun i => (hbound i _).shrink_scale hτ.le hτs) (fun i => hx i _) (fun i => hy i _)
  · intro m
    exact he₂ m G (X+Y) hG (hX.add hY) τ ε δ hτ hτ1 hε hε1 hδ hsmall hseg
      (fun i t ht => hsegb i _ t ht) (fun i => hc i _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
