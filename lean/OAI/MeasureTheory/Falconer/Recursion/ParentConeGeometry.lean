import OAI.MeasureTheory.Falconer.Estimates.SourceStrongSeparation
import OAI.MeasureTheory.Falconer.Angular.CircleRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

namespace PlanarFalconer
open Set

theorem DyadicSquare.dist_center_le_three_quarters (Q : DyadicSquare)
    (hQ : 0 ≤ Q.side) {x : Plane} (hx : x ∈ Q.carrier) :
    dist x Q.center ≤ 3/4*Q.side := by
  have h0 : |x 0 - Q.center 0| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2.1]
  have h1 : |x 1 - Q.center 1| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [sq_nonneg Q.side, dist_nonneg (x := x) (y := Q.center)]

theorem strong_separation_direction_chord (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    dist (sourceRadialUnit y x) (sourceRadialUnit Q.center P.center) ≤ 1/32 := by
  have hs : 0 < s := hP.trans_le hp
  have hc : P.center ≠ Q.center := dist_pos.mp ((by positivity : 0 < 100*s).trans_le hl)
  have hx' := P.dist_center_le_three_quarters hP.le hx
  have hy' := Q.dist_center_le_three_quarters hQ.le hy
  have ht := dist_triangle P.center x Q.center
  have ht' := dist_triangle x y Q.center
  rw [dist_comm P.center x] at ht
  have hdist : 96*s ≤ dist x y := by linarith
  have hxy : x ≠ y := dist_pos.mp ((by positivity : 0 < 96*s).trans_le hdist)
  have he := endpoint_direction_dist_le (x := y) (y := x)
    (c := Q.center) (d := P.center) hxy hc
  rw [dist_comm y x] at he
  apply he.trans
  apply (div_le_iff₀ (dist_pos.mpr hxy)).mpr
  linarith

theorem small_chord_principal_angle {φ : ℝ} (hφ : |φ| ≤ Real.pi)
    (hd : dist (sourceUnitDirection φ) (sourceUnitDirection 0) ≤ 1/32) :
    |φ| ≤ 1/20 := by
  have he := sourceUnitDirection_dist_sq φ 0
  simp only [sub_zero] at he
  have hd2 := (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ) ≤ 1/32)).mpr hd
  have hc := Real.cos_le_one_sub_mul_cos_sq hφ
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg Real.pi)
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hid : Real.pi^2 * (1-2/Real.pi^2*φ^2) = Real.pi^2-2*φ^2 := by
    field_simp
  rw [hid] at hm
  have hc0 : 0 ≤ 1-Real.cos φ := sub_nonneg.mpr (Real.cos_le_one φ)
  have hpi : Real.pi^2 ≤ (16/5:ℝ)^2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hb := mul_le_mul_of_nonneg_left (show 1-Real.cos φ ≤ (1:ℝ)/2048 by nlinarith) (sq_nonneg Real.pi)
  have ha := sq_abs φ
  nlinarith [abs_nonneg φ]

noncomputable def sourceParentAxis (P Q : DyadicSquare) : ℝ :=
  sourceAngle (sourceRadialUnit Q.center P.center)

theorem strong_separation_parent_angle (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    ∃ φ : ℝ, |φ| ≤ 1/20 ∧
      sourceUnitDirection φ = sourceCircleRotate (-sourceParentAxis P Q) (sourceRadialUnit y x) ∧
      x-y = ‖x-y‖ • sourceDirection (φ+sourceParentAxis P Q) := by
  let axis := sourceParentAxis P Q
  let e := sourceRadialUnit Q.center P.center
  let dir := sourceCircleRotate (-axis) (sourceRadialUnit y x)
  let φ := sourceAngle dir
  have hφdir : sourceUnitDirection φ = dir := sourceUnitDirection_sourceAngle dir
  have hzero : sourceCircleRotate (-axis) e = sourceUnitDirection 0 := by
    change sourceUnitDirection (sourceAngle e + -sourceAngle e) = _
    rw [add_neg_cancel]
  have hchord := strong_separation_direction_chord P Q hP hQ hp hq hl hx hy
  have hd : dist (sourceUnitDirection φ) (sourceUnitDirection 0) ≤ 1/32 := by
    rw [hφdir, ← hzero, sourceCircleRotate_dist]
    exact hchord
  have hφpi : |φ| ≤ Real.pi := by
    exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  refine ⟨φ, small_chord_principal_angle hφpi hd, hφdir, ?_⟩
  have hrot := congrArg (sourceCircleRotate axis) hφdir
  simp only [dir, sourceCircleRotate_comp, sourceCircleRotate_add,
    neg_add_cancel, sourceCircleRotate_zero] at hrot
  have hv := congrArg (fun d : UnitCircle => (d : Plane)) hrot
  change sourceDirection (φ+axis) = sourceRadialVector y x at hv
  have hs : 0 < s := hP.trans_le hp
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht := dist_triangle P.center x Q.center
  have ht' := dist_triangle x y Q.center
  rw [dist_comm P.center x] at ht
  have hdist : 0 < dist x y := by linarith
  have hxy : x ≠ y := dist_pos.mp hdist
  rw [hv, sourceRadialVector, ite_eq_right hxy, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]

end PlanarFalconer

end OAI
