import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma coordinate_ball_root_volume (n : ℕ) :
    volume (coordinateBall n (Real.sqrt n)) ≤ ENNReal.ofReal ((12:ℝ)^n) := by
  have hpoint (x : Fin n → ℝ) :
      (coordinateBall n (Real.sqrt n)).indicator (fun _ => (1:ℝ≥0∞)) x ≤
        ENNReal.ofReal (Real.exp n) * ∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/4)) := by
    by_cases hx : x ∈ coordinateBall n (Real.sqrt n)
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_sum, ← Real.exp_add]
      have hs : (∑ i, (x i)^2) ≤ n := by
        have hp := pow_le_pow_left₀ (norm_nonneg _) hx 2
        change coordinateNorm x ^ 2 ≤ (Real.sqrt (n:ℝ)) ^ 2 at hp
        rw [coordinateNorm_sq, Real.sq_sqrt (by positivity)] at hp
        exact hp
      have he : 1 ≤ Real.exp ((n:ℝ) + ∑ i, -(x i)^2/4) := by
        apply Real.one_le_exp_iff.mpr
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact_mod_cast (ENNReal.ofReal_le_ofReal he)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc
    volume (coordinateBall n (Real.sqrt n)) =
        ∫⁻ x : Fin n → ℝ, (coordinateBall n (Real.sqrt n)).indicator (fun _ => (1:ℝ≥0∞)) x := by
      rw [lintegral_indicator_const (measurableSet_coordinateBall _ _), one_mul]
    _ ≤ ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp n) *
        ∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/4)) := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp n) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^n := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume n (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
      simp
    _ ≤ ENNReal.ofReal (Real.exp n) * (4:ℝ≥0∞)^n := by
      gcongr
      exact lintegral_quarterGaussian_le
    _ ≤ ENNReal.ofReal ((12:ℝ)^n) := by
      have he : Real.exp (n:ℝ) ≤ (3:ℝ)^n := by
        rw [← mul_one (n:ℝ), Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le n
      calc
        _ ≤ ENNReal.ofReal ((3:ℝ)^n) * (4:ℝ≥0∞)^n := mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num), ← mul_pow]; norm_num

lemma cube_scaled_ball_volume (n : ℕ) (z : Space n) {r : ℝ} (hr : 0 < r) :
    volume (Metric.closedBall z (Real.sqrt n*r)) ≤ ENNReal.ofReal ((12:ℝ)^n*r^n) := by
  rw [Measure.addHaar_closedBall_center]
  have he : (WithLp.toLp 2 : (Fin n → ℝ) → Space n) ⁻¹' Metric.closedBall 0 (Real.sqrt n*r) =
      coordinateBall n (r*Real.sqrt n) := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right, coordinateBall, coordinateNorm, mul_comm]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage (show NullMeasurableSet (Metric.closedBall (0:Space n) (Real.sqrt n*r)) volume from Metric.isClosed_closedBall.measurableSet.nullMeasurableSet), he,
    volume_coordinateBall_smul n r (Real.sqrt n) hr]
  calc
    _ ≤ ENNReal.ofReal (r^n) * ENNReal.ofReal ((12:ℝ)^n) :=
      mul_le_mul' le_rfl (coordinate_ball_root_volume n)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma cubeBall_volume (d : ℕ) (z : Space (d/2)) {r : ℝ} (hr : 0 < r) :
    CubeLaw d (CubeBall d z r) ≤ ENNReal.ofReal ((12:ℝ)^(d/2)*r^(d/2)) := by
  rw [CubeLaw, comap_subtype_coe_apply (cubeSet_measurable _)]
  apply (measure_mono (show Subtype.val '' CubeBall d z r ⊆ Metric.closedBall z (Real.sqrt (d/2:ℕ)*r) from ?_)).trans
    (cube_scaled_ball_volume (d/2) z hr)
  rintro _ ⟨u,hu,rfl⟩
  exact hu

lemma cube_cap_local {d : ℕ} (hd : 2 ≤ d) (y : Space d) {ε : ℝ} (hε : 0 < ε) :
    CubeLocal (fun u => capWeight y ε (CubeEmbedding d u))
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ)) := by
  intro z r hr
  let A : Set (Cube d) := CubeEmbedding d ⁻¹' Metric.closedBall y ε
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet.preimage (cubeEmbedding_measurable d)
  have hint : (∫⁻ u in CubeBall d z r, capWeight y ε (CubeEmbedding d u) ∂CubeLaw d) =
      CubeLaw d (A ∩ CubeBall d z r) := by
    change (∫⁻ u in CubeBall d z r, A.indicator (fun _ => (1:ℝ≥0∞)) u ∂CubeLaw d) = _
    rw [lintegral_indicator_const hA, one_mul, Measure.restrict_apply hA]
  rw [hint]
  have hεball : A ⊆ CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d y) ε := by
    intro u hu
    exact (cubeProject_parameter_dist hd u y).trans
      (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))
  have hs : (0:ℝ) ≤ (d/2:ℕ)/4 := by positivity
  have ht : (0:ℝ) ≤ 3*(d/2:ℕ)/4 := by positivity
  have he (t : ℝ) (ht : 0 < t) : t^(d/2) = t^((d/2:ℕ)/4:ℝ)*t^(3*(d/2:ℕ)/4:ℝ) := by
    rw [← Real.rpow_add ht, show ((d/2:ℕ)/4:ℝ)+(3*(d/2:ℕ)/4:ℝ) = (d/2:ℕ) by ring, Real.rpow_natCast]
  by_cases hh : r ≤ ε
  · apply ((measure_mono Set.inter_subset_right).trans (cubeBall_volume d z hr)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he r hr, ← mul_assoc]
    gcongr
  · apply ((measure_mono (Set.inter_subset_left.trans hεball)).trans
      (cubeBall_volume d (Real.sqrt (d/2:ℕ) • cubeProject d y) hε)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he ε hε, ← mul_assoc]
    gcongr
    exact le_of_not_ge hh

lemma cubeBall_univ (d : ℕ) : CubeBall d 0 1 = Set.univ := by
  ext u
  simp only [Set.mem_univ, iff_true]
  change dist u.val 0 ≤ Real.sqrt (d/2:ℕ)*1
  rw [dist_zero_right, mul_one]
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [← pow_two]
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin (d/2), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := u.property i
      have hab := abs_le.mp h
      simp only [Real.norm_eq_abs, sq_abs]
      nlinarith
    _ = _ := by simp

lemma cube_mass_bound {d : ℕ} {f : Cube d → ℝ≥0∞} {L : ℝ} (h : CubeLocal f L) :
    (∫⁻ u, f u ∂CubeLaw d) ≤ ENNReal.ofReal L := by
  simpa [cubeBall_univ] using h 0 1 zero_lt_one

end MemoryPrecision


end

end OAI
