import OAI.Geometry.EinsteinFour.FrameBundle
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The actual orientation double cover, obtained by applying the determinant
sign representation to the tangent bundle's transition functions. Its two-point
fibers are glued by the genuine derivatives of chart changes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private abbrev TC := tangentBundleCore I4 M
private abbrev CI := atlas FourSpace M

/-- Determinant of the actual tangent transition, from chart `i` to chart `j`. -/
def orientationTransitionDet (i j : CI (M := M)) (x : M) : ℝ :=
  ((TC (M := M)).coordChange i j x).det

theorem orientationTransitionDet_self (i : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source) : orientationTransitionDet i i x = 1 := by
  have h : (TC (M := M)).coordChange i i x = ContinuousLinearMap.id ℝ FourSpace := by
    apply ContinuousLinearMap.ext
    intro v
    exact (TC (M := M)).coordChange_self i x hx v
  unfold orientationTransitionDet
  rw [h]
  exact LinearMap.det_id

theorem orientationTransitionDet_comp (i j k : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source ∩ k.val.source) :
    orientationTransitionDet i k x =
      orientationTransitionDet j k x * orientationTransitionDet i j x := by
  have h := (TC (M := M)).coordChange_linear_comp i j k x hx
  unfold orientationTransitionDet
  rw [← h]
  exact LinearMap.det_comp _ _

theorem orientationTransitionDet_ne_zero (i j : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) : orientationTransitionDet i j x ≠ 0 := by
  have h := orientationTransitionDet_comp i j i (show x ∈ i.val.source ∩ j.val.source ∩ i.val.source from ⟨hx, hx.1⟩)
  rw [orientationTransitionDet_self i hx.1] at h
  intro hz
  rw [hz, mul_zero] at h
  exact one_ne_zero h

theorem orientationTransitionDet_continuousOn (i j : CI (M := M)) :
    ContinuousOn (orientationTransitionDet i j) (i.val.source ∩ j.val.source) :=
  ContinuousLinearMap.continuous_det.comp_continuousOn ((TC (M := M)).continuousOn_coordChange i j)

private def orientationSignChange (a : ℝ) (s : Bool) : Bool := if 0 < a then s else !s

private theorem orientationSignChange_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s : Bool) :
    orientationSignChange b (orientationSignChange a s) = orientationSignChange (b * a) s := by
  by_cases hpa : 0 < a <;> by_cases hpb : 0 < b
  · simp only [orientationSignChange, ite_eq_left hpa, ite_eq_left hpb, ite_eq_left (mul_pos hpb hpa)]
  · have hbn : b < 0 := lt_of_le_of_ne (le_of_not_gt hpb) hb
    simp only [orientationSignChange, ite_eq_left hpa, ite_eq_right hpb,
      ite_eq_right (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hbn.le hpa.le))]
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
    simp only [orientationSignChange, ite_eq_right hpa, ite_eq_left hpb,
      ite_eq_right (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hpb.le han.le))]
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
    have hbn : b < 0 := lt_of_le_of_ne (le_of_not_gt hpb) hb
    simp only [orientationSignChange, ite_eq_right hpa, ite_eq_right hpb,
      ite_eq_left (mul_pos_of_neg_of_neg hbn han), Bool.not_not]

private theorem orientationTransition_continuousOn (i j : CI (M := M)) :
    ContinuousOn (fun p : M × Bool => orientationSignChange (orientationTransitionDet i j p.1) p.2)
      ((i.val.source ∩ j.val.source) ×ˢ univ) := by
  intro p hp
  have hd : ContinuousWithinAt (fun q : M × Bool => orientationTransitionDet i j q.1)
      ((i.val.source ∩ j.val.source) ×ˢ univ) p :=
    ((orientationTransitionDet_continuousOn i j).comp continuousOn_fst
      (fun _ h => h.1)) p hp
  by_cases hpos : 0 < orientationTransitionDet i j p.1
  · apply continuousWithinAt_snd.congr_of_eventuallyEq
    · filter_upwards [hd.eventually (Ioi_mem_nhds hpos)] with q hq
      exact ite_eq_left hq
    · exact ite_eq_left hpos
  · have hn : orientationTransitionDet i j p.1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (orientationTransitionDet_ne_zero i j hp.1)
    have hc : Continuous (fun q : M × Bool => !q.2) := by fun_prop
    apply hc.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [hd.eventually (Iio_mem_nhds hn)] with q hq
      exact ite_eq_right (not_lt.mpr hq.le)
    · exact ite_eq_right hpos

/-- The orientation cover is a bundle with the determinant-sign cocycle. -/
def orientationCoverCore : FiberBundleCore (CI (M := M)) M Bool where
  baseSet i := i.val.source
  isOpen_baseSet i := i.val.open_source
  indexAt := (TC (M := M)).indexAt
  mem_baseSet_at := (TC (M := M)).mem_baseSet_at
  coordChange i j x := orientationSignChange (orientationTransitionDet i j x)
  coordChange_self i x hx s := by
    rw [orientationTransitionDet_self i hx]
    simp [orientationSignChange]
  continuousOn_coordChange := orientationTransition_continuousOn
  coordChange_comp i j k x hx s := by
    rw [orientationTransitionDet_comp i j k hx]
    exact orientationSignChange_mul (orientationTransitionDet_ne_zero i j hx.1)
      (orientationTransitionDet_ne_zero j k ⟨hx.1.2, hx.2⟩) s

abbrev OrientationCover (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] := (orientationCoverCore (M := M)).TotalSpace

/-- The projection has exactly two sheets, with actual bundle trivializations. -/
theorem orientationCover_isCoveringMap :
    IsCoveringMap (orientationCoverCore (M := M)).proj := by
  apply IsCoveringMap.mk (orientationCoverCore (M := M)).proj (fun _ : M => Bool)
    (fun x => (orientationCoverCore (M := M)).localTrivAt x)
  exact (orientationCoverCore (M := M)).mem_baseSet_at

end
end PositiveEinsteinFour.Geometry

end OAI
