import OAI.Geometry.SurfaceImmersion.Geometry.CompactCompositionPrefix
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

theorem nonlinear_lowJet_neighborhood_of_C2 (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {Q O : Set LowJet} (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A.jetChartMap i F ∘ T)) S Q) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q' ⊆ O ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
        A.WeightedBound 1 2 ρ (G-F) → MapsTo (lowJet (A.jetChartMap i G ∘ T)) S Q' := by
  obtain ⟨r,Q',hr,hQ',_,hQ'O,hnear⟩ := exists_lowJet_segment_margin hQ hO hQO
  obtain ⟨Dr,hDr,hd⟩ := A.jetPlaneRead_bound i 2
  obtain ⟨Dc,hDc,hc⟩ := compact_composition_prefix hT hS hSc 0
  let ρ := r/(1+Dc*Dr)
  have hDc0 : 0 ≤ Dc := zero_le_one.trans hDc
  have hρ : 0 < ρ := div_pos hr (by positivity)
  refine ⟨ρ,Q',hρ,hQ',hQ'O,?_⟩
  intro G hG hclose
  have hdiff := hd (G-F) (hG.sub hF) 1 ρ zero_lt_one le_rfl hρ.le hclose
  have hglobal := weightedBound_comp_isometry planeCoordinateIsometry
    ((A.jetChartMap_smooth i (hG.sub hF)).comp planeCoordinateIsometry.symm.contDiff) hdiff
  have heq : (A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘
      planeCoordinateIsometry = A.jetChartMap i (G-F) := by funext x; simp
  change WeightedEstimates.WeightedBound univ 1 2 (Dr*ρ)
    ((A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry) at hglobal
  rw [heq] at hglobal
  have hcomp := hc (A.jetChartMap i (G-F)) 1 (Dr*ρ) zero_lt_one (by positivity)
    (A.jetChartMap_smooth i (hG.sub hF)) (fun j hj => by
      simpa only [one_pow,div_one] using hglobal.mono_order (by omega : j ≤ 2)) 2 (by omega)
  have hsmall : Dc*(Dr*ρ)/1^2 ≤ r := by
    simp only [one_pow,div_one]
    calc
      Dc*(Dr*ρ) ≤ (1+Dc*Dr)*ρ := by nlinarith [hρ.le]
      _ = r := by dsimp [ρ]; field_simp
  have hh := hnear hS ((A.jetChartMap_smooth i hF).comp hT)
    ((A.jetChartMap_smooth i (hG.sub hF)).comp hT) hFQ zero_lt_one le_rfl
    (show 0 ≤ Dc*(Dr*ρ) by positivity) hsmall
    (by simpa only [one_pow,div_one,Pi.sub_def] using hcomp) 1 ⟨by norm_num,le_rfl⟩
  have hsum : (fun p => (A.jetChartMap i F ∘ T) p+
      (1 : ℝ) • (A.jetChartMap i (G-F) ∘ T) p) = A.jetChartMap i G ∘ T := by
    have had := A.jetChartMap_add i F (G-F)
    have hfg : F+(G-F) = G := by abel
    rw [hfg] at had
    funext p
    simpa only [one_smul,Pi.add_apply,Function.comp_apply] using congrFun had.symm (T p)
  change MapsTo (lowJet (fun p => (A.jetChartMap i F ∘ T) p+
    (1 : ℝ) • (A.jetChartMap i (G-F) ∘ T) p)) S Q' at hh
  rw [hsum] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
