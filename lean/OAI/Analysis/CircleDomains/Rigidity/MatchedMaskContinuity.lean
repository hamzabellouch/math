import OAI.Analysis.CircleDomains.Topology.PlaneComponentRelation
import OAI.Analysis.CircleDomains.Rigidity.CorrespondenceMaskPlateau
import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonSystem

namespace OAI

/-! Continuity and open zero-cutoff neighborhoods of the actual matched
component mask. Point-to-disk pairs are handled by their whole source fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.mask_indexed_neighborhood (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1)
    (a : ℝ) (j : D.IndexedMatchedPair) :
    ∃ V : Set ℂ, IsOpen V ∧ closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ V ∧
      ContinuousOn (fun z => infiniteTracePrimitive cutoff (E.traceInterval hG hf φ L) a z
        (φ (D.selectedTarget hG hf (z : Sphere)))) V ∧
      ∀ z ∈ V, cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG hf (z : Sphere)) ∈ E.traceInterval hG hf φ L (Encodable.encode j) := by
  let n := Encodable.encode j
  let K := closedBall (E.sourceCenter j) (E.sourceRadius j)
  let Z := ball (E.sourceCenter j)
    (traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n)
  have hrad : E.sourceRadius j < traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n := by
    simpa only [n,traceRadius,traceEnumeration_encode] using
      traceBalloonRadius_inner (traceEnumeration_nonneg E.source_nonneg) m n
  have hKZ : K ⊆ Z := fun z hz => lt_of_le_of_lt hz hrad
  have hwidth : E.traceWidth L n = L*E.targetRadius j+traceExtraRadius n := by
    simp only [traceWidth,traceTargetRadius,n,traceEnumeration_encode]
  have hcenter : E.traceScalarCenter hG hf φ n = φ (E.targetCenter j : Sphere) := by
    simp only [traceScalarCenter,n,traceEnumeration_encode]
  apply correspondence_mask_plateau_neighborhood (D.planeRelation_closed hf)
    (fun z => D.selectedTarget_mem hG hf (z : Sphere)) hφ hc hcc E.traceCenter
    (nonnegative_square_summable_tendsto_zero (fun k => (traceBalloonRadius_pos m k).le)
      (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) m))
    (E.traceWidth_tendsto L) (by simpa only [dist_eq_norm,traceRadius] using hout)
    (fun _ => measurableSet_Ioo) (fun _ => by simp)
    (E.traceInterval_represents hG hf φ L) (isCompact_closedBall _ _) isOpen_ball hKZ
    (j := n) (by
      intro z hz
      apply hzero
      have hz' : ‖z-E.sourceCenter j‖ < traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n := by simpa only [mem_ball,dist_eq_norm] using hz
      simpa only [traceCenter,n,traceEnumeration_encode] using hz'.le)
    (η := traceExtraRadius n/2) (half_pos (traceExtraRadius_pos n)) rfl
    (β := E.traceScalarCenter hG hf φ n) (by
      exact ⟨sub_lt_self _ (E.traceWidth_pos L n),lt_add_of_pos_right _ (E.traceWidth_pos L n)⟩)
    (by
      intro z hz p hp
      have hz' : (z : Sphere) ∈ j.val.1 := by
        rw [E.source_eq]
        exact mem_image_of_mem _ hz
      have h := abs_le.mp (E.scalar_fiber_bound hL j hz' hp)
      rw [hcenter,hwidth]
      constructor <;> linarith [h.1,h.2,traceExtraRadius_pos n]) a

 theorem MatchedRoundDisks.mask_continuous (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1)
    (a : ℝ) : Continuous (fun z => infiniteTracePrimitive cutoff (E.traceInterval hG.1 hf φ L) a z
      (φ (D.selectedTarget hG.1 hf (z : Sphere)))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases D.plane_fiber_singleton_or_indexed hG hinf hf hG' hinf' z with hs | ⟨j,hj⟩
  · exact correspondence_mask_continuousAt_singleton (D.planeRelation_closed hf)
      (fun z => D.selectedTarget_mem hG.1 hf (z : Sphere)) hφ hc hcc E.traceCenter
      (nonnegative_square_summable_tendsto_zero (fun k => (traceBalloonRadius_pos m k).le)
        (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) m))
      (E.traceWidth_tendsto L) (by simpa only [dist_eq_norm,traceRadius] using hout)
      (fun _ => measurableSet_Ioo) (fun _ => by simp)
      (E.traceInterval_represents hG.1 hf φ L) hs a
  · obtain ⟨V,hV,hKV,hcont,_⟩ := E.mask_indexed_neighborhood hG.1 hf hφ hL m hc hcc hzero hout a j
    have hz : z ∈ V := by
      apply hKV
      rw [E.source_eq,OnePoint.coe_injective.mem_set_image] at hj
      exact hj
    exact hcont.continuousAt (hV.mem_nhds hz)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
