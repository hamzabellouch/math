import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.RealContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma real_terminal_cap {d : ℕ} (hd : 1 ≤ d) (y z : Space d)
    {ε r α : ℝ} (hε : 0 < ε) (hr : 0 < r) (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) :
    ((ambientSphereLaw (E := Space d)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3*4^d:ℝ) * ε^((d:ℝ)-1-α) * r^α) := by
  let : NeZero d := ⟨by omega⟩
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have hs : 0 ≤ (d:ℝ)-1-α := sub_nonneg.mpr hαn
  have he (t : ℝ) (ht : 0 < t) : t^(d-1) = t^((d:ℝ)-1-α)*t^α := by
    rw [← Real.rpow_add ht, sub_add_cancel, ← hn, Real.rpow_natCast]
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · calc
      _ ≤ ambientSphereLaw (E := Space d) (Metric.closedBall z r) := measure_mono Set.inter_subset_left
      _ ≤ ENNReal.ofReal ((3*4^d:ℝ)*r^(d-1)) := by
        simpa [ENNReal.ofReal_mul, finrank_euclideanSpace_fin] using
          ambientSphereLaw_closedBall (E := Space d) z hr (d-1) (by simp)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [he r hr, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le h hs) (by positivity)) (by positivity)
  · calc
      _ ≤ ambientSphereLaw (E := Space d) (Metric.closedBall y ε) := measure_mono Set.inter_subset_right
      _ ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
        simpa [ENNReal.ofReal_mul, finrank_euclideanSpace_fin] using
          ambientSphereLaw_closedBall (E := Space d) y hε (d-1) (by simp)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [he ε hε, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (le_of_not_ge h) hα) (by positivity)

lemma sphere_cap_real_mass {d : ℕ} (hd : 1 ≤ d) (y : Space d) {ε α : ℝ}
    (hε : 0 < ε) (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) :
    SphereBallBound (fun s => capWeight y ε s.val) ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)) α := by
  intro z r hr
  change (∫⁻ s in Subtype.val ⁻¹' Metric.closedBall z r,
    capWeight y ε s.val ∂sphereLaw) ≤ _
  rw [← setLIntegral_map Metric.isClosed_closedBall.measurableSet (measurable_capWeight y ε)
    measurable_subtype_coe]
  change (∫⁻ s in Metric.closedBall z r, capWeight y ε s ∂ambientSphereLaw) ≤ _
  rw [← withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  change ((ambientSphereLaw (E := Space d)).withDensity
    ((Metric.closedBall y ε).indicator 1)) (Metric.closedBall z r) ≤ _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact real_terminal_cap hd y z hε hr hα hαn

lemma sphere_mass_bound {d : ℕ} {h : Sphere d → ℝ≥0∞} {H α : ℝ}
    (hh : SphereBallBound h H α) : (∫⁻ s, h s ∂SpherePrior d) ≤ ENNReal.ofReal H := by
  have he : {s : Sphere d | dist s.val (0:Space d) ≤ 1} = Set.univ := by
    ext s
    simp [dist_zero_right]
  simpa [SphereBallBound, he] using hh 0 1 zero_lt_one

lemma real_continuation_cap_integral {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N} (hδ : ∀ n j, Measurable (δ n j))
    (y : ℕ → Fin N → Space d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) (n k : ℕ) (j : Fin N) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s.val ∂SpherePrior d) ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d N ^ BlockCount k (d/8)) := by
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  apply sphere_mass_bound
  apply real_continuation_mass hd hN hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _) (by positivity) hαlo hαhi
    (fun n j => sphere_cap_real_mass (by omega) (y n j) hε (by linarith) (by linarith))
  simpa [mul_comm] using blockCount_mul_ge k (by omega : 0 < d/8)

end MemoryPrecision


end

end OAI
