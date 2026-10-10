import OAI.Analysis.CircleDomains.Sobolev.SquarePoincareEnergy
import OAI.Analysis.CircleDomains.Modulus.SquareQuarterOscillation

namespace OAI

/-! A point with value at least one and small coarse average forces
quantitative Sobolev energy on one of its shrinking coordinate squares. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_capacity_scale {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) (hc : 1 ≤ u (euclideanPlaneCoordinates.symm c))
    (hmean : |squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 1/2) :
    ∃ n : ℕ, (1/128:ℝ)^2 * (1/4:ℝ)^n ≤
      ∫ p in coordinateSquare c ((1/4:ℝ)^n),
        (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2 := by
  by_contra! hn
  have hosc (n : ℕ) :
      (⨍ p in coordinateSquare c (1*(1/4:ℝ)^n),
        |u (euclideanPlaneCoordinates.symm p)-
          squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c (1*(1/4:ℝ)^n)|) ≤
        (1/128:ℝ)*(1/2:ℝ)^n := by
    have he := locally_sobolev_square_oscillation_sq hu hw hLp c
      (pow_pos (by norm_num : (0:ℝ)<1/4) n)
    have hp : ((1/2:ℝ)^n)^2 = (1/4:ℝ)^n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hb : 0 ≤ (1/128:ℝ)*(1/2:ℝ)^n := by positivity
    simp only [one_mul]
    nlinarith [hn n]
  have hpoint := square_point_average_bound_quarters
    (hu.comp euclideanPlaneCoordinates.symm.continuous) c (by norm_num : (0:ℝ)<1) hosc
  have hmean' := (le_abs_self (squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1)).trans hmean
  have hl := le_abs_self (u (euclideanPlaneCoordinates.symm c)-
    squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1)
  change |u (euclideanPlaneCoordinates.symm c)-
    squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 32*(1/128:ℝ) at hpoint
  norm_num at hpoint
  linarith

end CircleDomainRigidity

end

end OAI
