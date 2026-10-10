import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevPoincare

namespace OAI

/-! Coordinate squares, their exact areas, and the actual Sobolev Poincare estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def coordinateSquare (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) := closedBall c r

lemma coordinateSquare_eq_rectangle (c : ℝ × ℝ) (r : ℝ) :
    coordinateSquare c r = Icc (c.1-r) (c.1+r) ×ˢ Icc (c.2-r) (c.2+r) := by
  change closedBall (c.1,c.2) r = _
  rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]

lemma coordinateSquare_compact (c : ℝ × ℝ) (r : ℝ) : IsCompact (coordinateSquare c r) :=
  isCompact_closedBall c r

lemma coordinateSquare_real_volume (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateSquare c r) = 4*r^2 := by
  rw [coordinateSquare_eq_rectangle]
  have h0 : c.1-r ≤ c.1+r := by linarith
  have h1 : c.2-r ≤ c.2+r := by linarith
  rw [Measure.volume_eq_prod, measureReal_prod_prod,
    Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1]
  ring

lemma coordinateSquare_volume_ne_zero (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    volume (coordinateSquare c r) ≠ 0 := by
  intro hz
  have he := coordinateSquare_real_volume c hr.le
  rw [measureReal_def, hz, ENNReal.toReal_zero] at he
  nlinarith [sq_pos_of_pos hr]

lemma locally_sobolev_square_poincare {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      (⨍ q in coordinateSquare c r, u (euclideanPlaneCoordinates.symm q))|) ≤
    2*r*(⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) := by
  have h0 : c.1-r < c.1+r := by linarith
  have h1 : c.2-r < c.2+r := by linarith
  have h := locally_sobolev_rectangular_poincare hu hw hLp h0 h1
  dsimp only at h
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod,
    ← coordinateSquare_eq_rectangle] at h
  have hI (i : Fin 2) : IntegrableOn
      (fun p => |V (euclideanPlaneCoordinates.symm p) i|) (coordinateSquare c r) volume :=
    (local_partial_coordinate_integrableOn hLp (coordinateSquare_compact c r) i).abs
  have he : (⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) =
      (⨍ p in coordinateSquare c r, |V (euclideanPlaneCoordinates.symm p) 0|)+
      (⨍ p in coordinateSquare c r, |V (euclideanPlaneCoordinates.symm p) 1|) := by
    simpa only [Pi.add_apply] using average_add (hI 0) (hI 1)
  rw [he]
  convert h using 1
  ring

end CircleDomainRigidity

end

end OAI
