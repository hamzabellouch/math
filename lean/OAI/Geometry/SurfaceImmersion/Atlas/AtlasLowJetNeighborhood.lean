import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetReadBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetSegment

namespace OAI

/-! A fixed compact admissible neighborhood for the primitive's slow maps,
obtained from the global C2 displacement estimate. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem lowJet_neighborhood_of_C2 (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {S : Set JetPolynomial.Base} (hS : IsOpen S)
    {Q O : Set LowJet} (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A.jetChartMap i F)) S Q) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q' ⊆ O ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
        A.WeightedBound 1 2 ρ (G-F) → MapsTo (lowJet (A.jetChartMap i G)) S Q' := by
  obtain ⟨r,Q',hr,hQ',_,hQ'O,hnear⟩ := exists_lowJet_segment_margin hQ hO hQO
  obtain ⟨D,hD,hd⟩ := A.jetPlaneRead_bound i 2
  let ρ := r/(1+D)
  have hρ : 0 < ρ := div_pos hr (by positivity)
  refine ⟨ρ,Q',hρ,hQ',hQ'O,?_⟩
  intro G hG hclose
  have hdiff := hd (G-F) (hG.sub hF) 1 ρ zero_lt_one le_rfl hρ.le hclose
  have hc := weightedBound_comp_isometry planeCoordinateIsometry
    ((A.jetChartMap_smooth i (hG.sub hF)).comp planeCoordinateIsometry.symm.contDiff) hdiff
  have he : (A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘
      planeCoordinateIsometry = A.jetChartMap i (G-F) := by
    funext x
    simp
  change WeightedEstimates.WeightedBound univ 1 2 (D*ρ)
    ((A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry) at hc
  rw [he] at hc
  have hc' : WeightedEstimates.WeightedBound S 1 2 (D*ρ) (A.jetChartMap i (G-F)) :=
    hc.restrict_open hS
  have hsmall : D*ρ/1^2 ≤ r := by
    dsimp [ρ]
    have hh : r/(1+D)*(1+D) = r := div_mul_cancel₀ r (by positivity)
    simp only [one_pow,div_one]
    nlinarith [div_nonneg hr.le (show 0 ≤ 1+D by positivity)]
  have hh := hnear hS (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i (hG.sub hF))
    hFQ zero_lt_one le_rfl (mul_nonneg hD hρ.le) hsmall hc' 1 ⟨by norm_num,le_rfl⟩
  have hsum : (fun p => A.jetChartMap i F p+(1 : ℝ) • A.jetChartMap i (G-F) p) =
      A.jetChartMap i G := by
    have had := A.jetChartMap_add i F (G-F)
    have hfg : F+(G-F) = G := by abel
    rw [hfg] at had
    funext p
    simpa only [one_smul,Pi.add_apply] using congrFun had.symm p
  change MapsTo (lowJet (fun p => A.jetChartMap i F p+(1 : ℝ) • A.jetChartMap i (G-F) p)) S Q' at hh
  exact Eq.mp (congrArg (fun f : JetPolynomial.Base → JetPolynomial.Space => MapsTo (lowJet f) S Q') hsum) hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
