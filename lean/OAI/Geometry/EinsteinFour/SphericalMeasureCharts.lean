import OAI.Geometry.EinsteinFour.SphericalMeasureInvariance
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! Compact smooth coordinate-face charts and a Lipschitz projection for the
actual unit three-sphere. These are used only to establish finite positive
Hausdorff mass; no spherical integration formula is assumed. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators ContDiff Topology NNReal

noncomputable section

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

def faceSign (t : Bool) : ℝ := if t then 1 else -1

theorem faceSign_ne_zero (t : Bool) : faceSign t ≠ 0 := by
  cases t <;> norm_num [faceSign]

def faceVector (i : Fin 4) (t : Bool) (u : ThreeSpace) : FourSpace :=
  WithLp.toLp 2 (Fin.insertNth i (faceSign t) (fun j => u j))

theorem faceVector_ne_zero (i : Fin 4) (t : Bool) (u : ThreeSpace) :
    faceVector i t u ≠ 0 := by
  intro h
  have hi := congrArg (fun v : FourSpace => v i) h
  exact faceSign_ne_zero t (by simpa [faceVector] using hi)

theorem faceVector_contDiff (i : Fin 4) (t : Bool) :
    ContDiff ℝ ∞ (faceVector i t) := by
  apply (contDiff_piLp (p := (2 : ENNReal))).mpr
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · simpa only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ThreeSpace => faceSign t))
  · simpa only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_succAbove] using
      (contDiff_piLp_apply (p := (2 : ENNReal)) (i := j) :
        ContDiff ℝ ∞ (fun u : ThreeSpace => u j))

def faceChart (i : Fin 4) (t : Bool) (u : ThreeSpace) : FourSpace :=
  ‖faceVector i t u‖⁻¹ • faceVector i t u

theorem faceChart_contDiff (i : Fin 4) (t : Bool) : ContDiff ℝ ∞ (faceChart i t) := by
  have hf := faceVector_contDiff i t
  have hn := hf.norm ℝ (faceVector_ne_zero i t)
  exact (hn.inv (fun u => norm_ne_zero_iff.mpr (faceVector_ne_zero i t u))).smul hf

theorem faceChart_lipschitz (i : Fin 4) (t : Bool) :
    ∃ K : ℝ≥0, LipschitzOnWith K (faceChart i t) (Metric.closedBall (0 : ThreeSpace) 2) :=
  (faceChart_contDiff i t).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)

/-- The eight normalized cube faces cover the sphere using a fixed compact
three-dimensional parameter ball. -/
theorem exists_faceChart (q : Directions) :
    ∃ i : Fin 4, ∃ t : Bool, ∃ u ∈ Metric.closedBall (0 : ThreeSpace) 2,
      faceChart i t u = q.val := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => |q.val i|) Finset.univ_nonempty
  have hmax (j : Fin 4) : |q.val j| ≤ |q.val i| := hi j (Finset.mem_univ j)
  have hqi : q.val i ≠ 0 := by
    intro he
    have hz : q.val = 0 := by
      ext j
      exact abs_eq_zero.mp (le_antisymm (by simpa [he] using hmax j) (abs_nonneg _))
    have := q.property
    rw [hz, norm_zero] at this
    norm_num at this
  have ha : 0 < |q.val i| := abs_pos.mpr hqi
  obtain ⟨t, ht⟩ : ∃ t : Bool, faceSign t = q.val i / |q.val i| := by
    by_cases hp : 0 < q.val i
    · refine ⟨true, ?_⟩
      simp [faceSign, abs_of_pos hp, hqi]
    · have hn : q.val i < 0 := lt_of_le_of_ne (le_of_not_gt hp) hqi
      refine ⟨false, ?_⟩
      simp [faceSign, abs_of_neg hn, hqi]
  let u : ThreeSpace := WithLp.toLp 2 (fun j => q.val (i.succAbove j) / |q.val i|)
  have hub (j : Fin 3) : |u j| ≤ 1 := by
    change |q.val (i.succAbove j) / (|q.val i|)| ≤ 1
    rw [abs_div, abs_abs, div_le_one ha]
    exact hmax _
  have husq : ‖u‖ ^ 2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h := hub j
        have hn := abs_nonneg (u j)
        nlinarith [sq_abs (u j)]
      _ = 3 := by norm_num
  have hu : u ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg u]
  have hraw : faceVector i t u = |q.val i|⁻¹ • q.val := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_same,
        ht, PiLp.smul_apply, smul_eq_mul]
      ring
    · simp only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_succAbove,
        u, PiLp.smul_apply, smul_eq_mul]
      ring
  refine ⟨i, t, u, hu, ?_⟩
  unfold faceChart
  rw [hraw, norm_smul_of_nonneg (inv_nonneg.mpr ha.le), q.property, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- Dropping one coordinate does not increase Euclidean distance. -/
def tailProjection (v : FourSpace) : ThreeSpace :=
  WithLp.toLp 2 (fun j => v j.succ)

theorem tailProjection_norm_le (v : FourSpace) : ‖tailProjection v‖ ≤ ‖v‖ := by
  have h : ‖v‖ ^ 2 = (v 0) ^ 2 + ‖tailProjection v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
      EuclideanSpace.real_norm_sq_eq]
    rfl
  nlinarith [sq_nonneg (v 0), norm_nonneg v, norm_nonneg (tailProjection v)]

theorem tailProjection_lipschitz : LipschitzWith 1 tailProjection := by
  apply LipschitzWith.mk_one
  intro v w
  rw [dist_eq_norm, dist_eq_norm]
  have he : tailProjection v - tailProjection w = tailProjection (v - w) := rfl
  rw [he]
  exact tailProjection_norm_le (v - w)

/-- The projection of the actual sphere contains a nonempty open ball. -/
theorem ball_subset_tailProjection_sphere :
    Metric.ball (0 : ThreeSpace) 1 ⊆
      tailProjection '' {v : FourSpace | ‖v‖ = 1} := by
  intro u hu
  have hnorm : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hrad : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  let v : FourSpace := WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - ‖u‖ ^ 2)) (fun j => u j))
  have hv : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    change (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 + (∑ j : Fin 3, (u j) ^ 2) = 1
    rw [Real.sq_sqrt hrad, ← EuclideanSpace.real_norm_sq_eq u]
    ring
  refine ⟨v, ?_, ?_⟩
  · change ‖v‖ = 1
    nlinarith [norm_nonneg v]
  · ext j
    rfl

end
end PositiveEinsteinFour.Angular

end OAI
