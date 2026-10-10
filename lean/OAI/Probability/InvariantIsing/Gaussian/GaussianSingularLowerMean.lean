import OAI.Probability.InvariantIsing.Gaussian.GaussianFiniteColumnMinimum
import OAI.Probability.InvariantIsing.Core.DenseFiniteMinimum
import OAI.Probability.InvariantIsing.Gaussian.GaussianNormLowerMean

namespace OAI

/-! The Gaussian least singular value has the sharp asymptotic lower mean bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

theorem gaussianPatternSingularMin_mean_ge {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    Real.sqrt ((N : ℝ)-1)-Real.sqrt m ≤
      ∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMin z ∂stdGaussian _ := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1
  let : Nonempty S := by
    obtain ⟨x⟩ := unitVector_nonempty (EuclideanSpace ℝ (Fin m))
    exact ⟨⟨x.1,by simpa only [S,Metric.mem_sphere,dist_zero_right] using x.2⟩⟩
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  have hn (i : ℕ) : ‖(s i).1‖ = 1 := by
    simpa only [S,Metric.mem_sphere,dist_zero_right] using (s i).2
  let F (n : ℕ) (z : EuclideanSpace ℝ (Fin N × Fin m)) :=
    prefixMinimum (fun i => ‖gaussianPatternEuclideanOperator z (s i).1‖) n
  have hlim (z : EuclideanSpace ℝ (Fin N × Fin m)) :
      Tendsto (fun n => F n z) atTop (𝓝 (gaussianPatternSingularMin z)) := by
    exact dense_prefixMinimum_tendsto s hs (fun x => ‖gaussianPatternEuclideanOperator z x.1‖)
      (by fun_prop) ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hbound (n : ℕ) (z : EuclideanSpace ℝ (Fin N × Fin m)) : |F n z| ≤ ‖z‖ := by
    obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin (n+1) => ‖gaussianPatternEuclideanOperator z (s i).1‖)
    change |Finset.univ.inf' Finset.univ_nonempty _| ≤ _
    rw [he,abs_of_nonneg (norm_nonneg _)]
    have h := gaussianPatternEuclideanOperator_bound z (s i).1
    simpa only [hn,mul_one] using h
  have hint := tendsto_integral_of_dominated_convergence (μ := stdGaussian _) norm
    (fun n => (show Continuous (F n) from
      Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ =>
        (continuous_gaussianPattern_apply (s i).1).norm)).aestronglyMeasurable)
    ((finiteGaussian_lipschitz_memLp_two
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : EuclideanSpace ℝ (Fin N × Fin m) → ℝ))).integrable
      (by norm_num))
    (fun n => ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbound n z))
    (ae_of_all _ hlim)
  have hb (n : ℕ) : Real.sqrt ((N : ℝ)-1)-Real.sqrt m ≤ ∫ z, F n z ∂stdGaussian _ := by
    have hc := gaussian_finite_column_minimum hN (fun i : Fin (n+1) => (s i).1)
      (fun i => hn i)
    have hl := gaussianNorm_lower_mean (ι := Fin N)
    simp only [Fintype.card_fin] at hl
    exact (sub_le_sub_right hl (Real.sqrt m)).trans hc
  exact ge_of_tendsto hint (Filter.Eventually.of_forall hb)

end InvariantIsing

end

end OAI
