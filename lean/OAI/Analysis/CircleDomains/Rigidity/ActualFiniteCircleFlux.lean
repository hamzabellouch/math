import OAI.Analysis.CircleDomains.Rigidity.ActualAxialCircleFlux

namespace OAI

/-! Adding the two actual axial inequalities gives the full outward
circle flux, with exactly sixteen times the remaining mixed-radius sum. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_finite_circle_flux [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W)
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 W) volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hin : ∀ j ∈ F, closedBall (E.sourceCenter j) (E.sourceRadius j+η) ⊆ ball 0 R)
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m) :
    quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
      2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
      (∑ j : F, quadrantFlux (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η))+
      16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  have h0 := D.actual_axial_circle_flux E hG hinf hf hfix hH hinf' hR hRW 0 (htrace 0) hρ F hη hd hin hone
  have h1 := D.actual_axial_circle_flux E hG hinf hf hfix hH hinf' hR hRW 1 (htrace 1) hρ F hη hd hin hone
  have hm := D.selectedPlane_measurable E hG hinf hf hfix hH hinf'
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG.1 hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have hout := axialCircleFlux_add hm 0 hR.le hB.le (fun z hz => (hbound z hz).le)
  have hinflux (j : F) := axialCircleFlux_add hm (E.sourceCenter j)
    (add_nonneg (E.source_nonneg j) hη.le) hB.le
    (fun z hz => (hbound z (ball_subset_closedBall (hin j j.property hz))).le)
  have hsum : (∑ j : F, axialCircleFlux 0 (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η))+
      (∑ j : F, axialCircleFlux 1 (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η)) =
      ∑ j : F, quadrantFlux (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hinflux j)
  linarith

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
