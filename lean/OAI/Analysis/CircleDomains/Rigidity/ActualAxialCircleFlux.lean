import OAI.Analysis.CircleDomains.Rigidity.ActualEnclosedCircleSlice
import OAI.Analysis.CircleDomains.Rigidity.IntegrableAxialRestriction
import OAI.Analysis.CircleDomains.Rigidity.EnclosedFluxIntegration

namespace OAI

/-! Actual finite-hole axial flux bound from the proved common-point
trace and the source differential. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_axial_circle_flux [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W) (i : Fin 2)
    (htrace : ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
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
    axialCircleFlux i (D.selectedPlane hG.1 hf) 0 R-
      (∑ j : F, axialCircleFlux i (D.selectedPlane hG.1 hf)
        (E.sourceCenter j) (E.sourceRadius j+η)) ≤
      (∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
        8*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  let q := (U ∩ closedBall 0 R).indicator
    (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
  have hU : MeasurableSet U := (hG.1.preimage OnePoint.continuous_coe).measurableSet
  have hq : Integrable q volume := (integrable_indicator_iff (hU.inter measurableSet_closedBall)).mpr
    (hρ.mono_set (inter_subset_inter_right U (closedBall_subset_ball hRW)))
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG.1 hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have ht := axialDiskToll_integrable i
    (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
    (fun j => E.sourceRadius j) (fun j => E.targetRadius j)
    (fun j => E.source_nonneg j) (fun j => E.target_nonneg j)
    (E.source_summable.comp_injective Subtype.val_injective)
    (E.target_summable.comp_injective Subtype.val_injective)
  have h := enclosed_flux_integration i
    (D.selectedPlane_measurable E hG hinf hf hfix hH hinf')
    (fun j : F => E.sourceCenter j) (fun j => E.sourceRadius j+η)
    hR.le (fun j => add_nonneg (E.source_nonneg j) hη.le) hB.le
    (fun z hz => (hbound z hz).le) (fun j => hin j j.property) hq
    (fun z => indicator_nonneg (fun z _ => norm_nonneg _) z) ht.1
    (fun y => tsum_nonneg (fun j => indicator_nonneg
      (fun _ _ => mul_nonneg (by norm_num) (E.target_nonneg j)) y)) ht.2 (by
      filter_upwards [htrace,
        axial_disk_tolls_summable_ae i E.sourceCenter E.sourceRadius E.targetRadius
          E.source_nonneg E.target_nonneg E.source_summable E.target_summable,
        integrable_axial_restriction_ae (hU.inter measurableSet_ball) hρ i] with y htrace htoll hline
      intro hy
      exact D.actual_enclosed_circle_slice E hG hinf hf hfix hH hinf' hR hRW i y hy
        htrace htoll hline F hη hd hin hone)
  dsimp only [q] at h
  rw [integral_indicator (hU.inter measurableSet_closedBall)] at h
  convert h using 1
  ring

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
