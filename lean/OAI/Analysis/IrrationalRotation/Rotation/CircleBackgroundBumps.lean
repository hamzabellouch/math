import OAI.Analysis.IrrationalRotation.Model.BackgroundData
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundBumps
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundCost

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233.BackgroundCost

local instance circleBackgroundBumpsFactOnePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  change volume ({x} : Set (AddCircle (1 : ℝ))) = 0
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem exists_backgroundBumpData (θ : ℝ) (hθ : Irrational θ) :
    Nonempty (BackgroundBumpData θ) := by
  classical
  let : NullSingletonClass circleMeasure := ⟨circleMeasure_singleton⟩
  let : circleMeasure.OuterRegular := by
    change (volume : Measure (AddCircle (1 : ℝ))).OuterRegular
    infer_instance
  have hinfinite : ¬ IsOfFinAddOrder (θ : Circle) := by
    rw [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
    rintro ⟨q, hq⟩
    exact hθ.ne_rat q (by simpa using hq.symm)
  have hinj : Function.Injective (fun n : ℕ => n • (θ : Circle)) :=
    injective_nsmul_iff_not_isOfFinAddOrder.2 hinfinite
  have hchoice (n : ℕ) := exists_bump_disjoint_images circleMeasure (0 : Circle)
    (fun (i : Fin (2 ^ (n + 2))) (x : Circle) => x + ((i : ℕ) + 1) • (θ : Circle))
    (fun i => isometry_add_right _) (by
      intro i j hij
      apply Fin.ext
      have he : (i : ℕ) + 1 = (j : ℕ) + 1 := hinj (by simpa using hij)
      omega)
    (R := 1 / ((n : ℝ) + 1)) (by positivity)
    (ε := (1 / 2 : ℝ≥0∞) ^ (n + 2) / (2 : ℝ≥0∞) ^ (n + 2))
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by finiteness))
  choose r v hr hcap hμ hv hva hbounds hsupp hdisj using hchoice
  refine ⟨{
    radius := r
    bump := v
    radius_pos := hr
    radius_lt := hcap
    continuous_bump := hv
    bump_zero := hva
    bump_bounds := hbounds
    bump_support := hsupp
    disjoint_translates := hdisj
    weighted_support_bound := ?_ }⟩
  have hterm (n : ℕ) :
      (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (r n)) ≤
        (1 / 2 : ℝ≥0∞) ^ (n + 2) := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (n + 2) *
          ((1 / 2 : ℝ≥0∞) ^ (n + 2) / (2 : ℝ≥0∞) ^ (n + 2)) :=
        mul_le_mul_right (hμ n).le _
      _ = _ := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  calc
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 2) := ENNReal.tsum_le_tsum hterm
    _ = 1 / 2 := by
      simp_rw [pow_add]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      norm_num
      rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

theorem BackgroundBumpData.radius_tendsto_zero {θ : ℝ} (d : BackgroundBumpData θ) :
    Tendsto d.radius atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (d.radius_pos n).le) (fun n => (d.radius_lt n).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Invariant233.BackgroundCost

end

end OAI
