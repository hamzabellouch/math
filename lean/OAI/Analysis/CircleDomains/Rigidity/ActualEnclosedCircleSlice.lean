import OAI.Analysis.CircleDomains.Topology.ActualFiniteDiskSlice
import OAI.Analysis.CircleDomains.Rigidity.EnclosedCrossingSum
import OAI.Analysis.CircleDomains.Rigidity.AxialClosedDiskIntegral

namespace OAI

/-! The exact finite-circle slice inequality for the selected matched
field and the actual zero-extended source differential. -/
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

 theorem actual_enclosed_circle_slice [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W) (i : Fin 2) (y : ℝ) (hy : y ∈ Ioo (-R) R)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 W} volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hin : ∀ j ∈ F, closedBall (E.sourceCenter j) (E.sourceRadius j+η) ⊆ ball 0 R)
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m) :
    axialBandIncrement i (D.selectedPlane hG.1 hf) 0 R y-
      (∑ j : F, axialBandIncrement i (D.selectedPlane hG.1 hf)
        (E.sourceCenter j) (E.sourceRadius j+η) y) ≤
      (∫ x, ({z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R).indicator
        (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖) (complexCoordinateLine i y x))+
        2*axialDiskToll i (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
          (fun j => E.sourceRadius j) (fun j => E.targetRadius j) y := by
  let a := (axialChord i 0 R y).1
  let b := (axialChord i 0 R y).2
  have hy' : y ∈ Icc (-R) R := Ioo_subset_Icc_self hy
  have hab : a < b := horizontalChord_strict _ (by simpa [axialSwap] using hy)
  have houter (x : ℝ) (hx : x ∈ Icc a b) : complexCoordinateLine i y x ∈ closedBall 0 R :=
    (mem_closedBall_iff_mem_axialChord i 0 hR.le (by simpa [transverseCoordinate] using hy')).mpr hx
  have hend (right : Bool) : dist (complexCoordinateLine i y (if right then b else a)) 0 = R :=
    axialChord_endpoint_dist i 0 hR.le (by simpa [transverseCoordinate] using hy') right
  have ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η) := by
    intro j hj hx
    have hn := hin j hj hx
    have he := hend false
    simp only [Bool.false_eq_true,ite_false] at he
    exact (not_lt_of_ge he.ge) hn
  have hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η) := by
    intro j hj hx
    have hn := hin j hj hx
    have he := hend true
    simp only [ite_true] at he
    exact (not_lt_of_ge he.ge) hn
  have h := D.actual_finite_disk_slice E hG hinf hf hfix hH hinf' W i i y htrace htoll hρ F hη hd hone hab
    (fun x hx => (closedBall_subset_ball hRW) (houter x hx)) ha hb
  change axialCircleIncrement i (D.selectedPlane hG.1 hf) 0 R y-
    (∑ j ∈ crossingDisks (fun j : F => axialSwap i (E.sourceCenter j)) (fun j => E.sourceRadius j+η) y a b,
      axialCircleIncrement i (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η) y) ≤ _ at h
  rw [enclosed_crossing_sum (κ := F) i (D.selectedPlane hG.1 hf)
    (fun j => E.sourceCenter j) (fun j => E.sourceRadius j+η) hR.le hy'
    (fun j => (hin j j.property).trans ball_subset_closedBall)] at h
  have he := axial_closed_disk_integral i y hR.le hy'
    (U := {z : ℂ | (z : Sphere) ∈ G})
    (hG.1.preimage OnePoint.continuous_coe).measurableSet
    (fun z : ℂ => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
  change (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
    ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) = _ at he
  rw [he] at h
  have hout : axialBandIncrement i (D.selectedPlane hG.1 hf) 0 R y =
      axialCircleIncrement i (D.selectedPlane hG.1 hf) 0 R y := by
    apply indicator_of_mem
    simpa [transverseCoordinate] using hy'
  rwa [← hout] at h

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
