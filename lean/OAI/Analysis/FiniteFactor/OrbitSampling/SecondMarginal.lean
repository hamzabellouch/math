import OAI.Analysis.FiniteFactor.OrbitSampling.UniformEvent
import OAI.Analysis.FiniteFactor.OrbitSampling.RotationTransport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

/-- The actual second marginal of one orbit summand, obtained by weighted
Haar transport and not supplied as an assumption. -/
theorem sourceSamplingSummand_second_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I stage θ n).map Prod.snd =
      sourceSamplingHaar.withDensity (fun y => ENNReal.ofReal
        (sourceSamplingWeight I stage θ n (coordinateRotate θ (-n) y))) := by
  unfold sourceSamplingSummand
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map measurable_snd hp]
  exact sourceSamplingHaar_rotate_withDensity θ n _
    (sourceSamplingWeight_measurable I stage θ n).ennreal_ofReal

/-- The actual second marginal is the second-oriented empirical density. -/
theorem sourceSamplingUntrimmed_second_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) :
    (sourceSamplingUntrimmed I stage θ).map Prod.snd =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage true (fun i => decide (i ∈ I))
          (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w (n : ℤ) := fun x => sourceSamplingWeight I stage θ n (coordinateRotate θ (-n) x)
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage true (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) =ᵐ[sourceSamplingHaar]
      (fun x => c*(∑ n ∈ S, ENNReal.ofReal (w n x))) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    have hw (n : ℤ) : sourceSamplingProduct stage true (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) n θ x = w n x := by
      apply Finset.prod_congr rfl
      intro i _
      have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hx i).1,(hx i).2.le⟩
      have hz : Int.fract (x i-Int.fract ((n : ℝ)*θ i)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
      simp only [samplingOrientedWeight,ite_true,hz,hx',and_self]
      rw [coordinateRotate_neg_phase]
    simp only [sourceSamplingEmpiricalDensity,hw]
    rw [div_eq_mul_inv,mul_comm,← one_div,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingWeight_bounds I stage θ n (coordinateRotate θ (-n) x)).1)]
  rw [withDensity_congr_ae hrep]
  ext A hA
  rw [Measure.map_apply measurable_snd hA]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n (Prod.snd ⁻¹' A) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.map_apply measurable_snd hA,sourceSamplingSummand_second_density]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    ((sourceSamplingWeight_measurable I stage θ n).comp (coordinateRotate_preserving θ (-n)).measurable).ennreal_ofReal)).symm

/-- Uniform L2 densities for the actual untrimmed second marginals. -/
theorem sourceSamplingUntrimmed_second_L2 (I : Finset SourceCoordinate) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map Prod.snd = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSamplingEmpiricalDensity_uniform true (fun i => decide (i ∈ I))
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)] with θ hθ
  obtain ⟨C,hC⟩ := hθ
  refine ⟨C,fun stage => ⟨_,sourceSamplingUntrimmed_second_density I stage θ,(hC stage).1,(hC stage).2⟩⟩

end
end FiniteFactor

end OAI
