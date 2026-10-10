import OAI.Analysis.FiniteFactor.OrbitSampling.UniformEvent
import OAI.Analysis.FiniteFactor.OrbitSampling.Measures

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

/-- The actual first marginal is the verified empirical interval-test density.
The whole-circle tests [0,1] are valid on the Haar cube. -/
theorem sourceSamplingUntrimmed_first_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) :
    (sourceSamplingUntrimmed I stage θ).map Prod.fst =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I))
          (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w (n : ℤ) := sourceSamplingWeight I stage θ n
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) =ᵐ[sourceSamplingHaar]
      (fun x => c*(∑ n ∈ S, ENNReal.ofReal (w n x))) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    have hw (n : ℤ) : sourceSamplingProduct stage false (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) n θ x = w n x := by
      apply Finset.prod_congr rfl
      intro i _
      have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hx i).1,(hx i).2.le⟩
      have hy : Int.fract (x i+Int.fract ((n : ℝ)*θ i)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
      simp only [samplingOrientedWeight, Bool.false_eq_true, ite_false, samplingTestedFirstWeight,
        hx', hy, and_self, ite_true]
    simp only [sourceSamplingEmpiricalDensity,hw]
    rw [div_eq_mul_inv,mul_comm,← one_div,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingWeight_bounds I stage θ n x).1)]
  rw [withDensity_congr_ae hrep]
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n (Prod.fst ⁻¹' A) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.map_apply measurable_fst hA,sourceSamplingSummand_first_marginal]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    (sourceSamplingWeight_measurable I stage θ n).ennreal_ofReal)).symm

/-- Uniform L2 densities for the actual untrimmed first marginals. -/
theorem sourceSamplingUntrimmed_first_L2 (I : Finset SourceCoordinate) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map Prod.fst = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSamplingEmpiricalDensity_uniform false (fun i => decide (i ∈ I))
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)] with θ hθ
  obtain ⟨C,hC⟩ := hθ
  refine ⟨C,fun stage => ⟨_,sourceSamplingUntrimmed_first_density I stage θ,(hC stage).1,(hC stage).2⟩⟩

end
end FiniteFactor

end OAI
