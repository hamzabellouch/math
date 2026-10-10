import OAI.Analysis.FiniteFactor.OrbitSampling.EmpiricalL2

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical Topology
noncomputable section

/-- Actual empirical L2 bounds, uniform over all stages on a conull event. -/
theorem sourceSamplingEmpiricalDensity_uniform (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      MemLp (sourceSamplingEmpiricalDensity stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) 2
          (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ∧
      (∫ x, sourceSamplingEmpiricalDensity stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤ C := by
  filter_upwards [sourceSamplingSquaredError_ae r b a c a' c'] with θ hθ
  let e := fun stage => sourceSamplingSquaredError stage r b
    (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ
  refine ⟨2*(∑' stage, e stage)+2*Real.exp 5,?_⟩
  intro stage
  refine ⟨sourceSamplingEmpiricalDensity_memLp stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) θ,?_⟩
  have he : e stage ≤ ∑' l, e l := hθ.1.le_tsum stage (fun l _ => sourceSamplingSquaredError_nonneg l r b _ _ θ)
  apply (sourceSamplingEmpiricalDensity_square_le stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) θ).trans
  change 2*e stage+2*Real.exp 5 ≤ _
  linarith

/-- A single event gives full sampling convergence and uniform empirical L2
bounds for every member of any countable source test family. -/
theorem sourceSampling_full_L2_event {ι : Type*} [Countable ι]
    (r : ι → Bool) (b : ι → SourceCoordinate → Bool)
    (a c a' c' : ι → SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ j,
      Tendsto (fun stage => sourceSamplingSquaredError stage (r j) (b j)
        (fun i => Set.Icc (a j i) (c j i)) (fun i => Set.Icc (a' j i) (c' j i)) θ) atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ stage,
        MemLp (sourceSamplingEmpiricalDensity stage (r j) (b j)
          (fun i => Set.Icc (a j i) (c j i)) (fun i => Set.Icc (a' j i) (c' j i)) θ) 2
            (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ∧
        (∫ x, sourceSamplingEmpiricalDensity stage (r j) (b j)
          (fun i => Set.Icc (a j i) (c j i)) (fun i => Set.Icc (a' j i) (c' j i)) θ x^2
          ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤ C := by
  apply ae_all_iff.mpr
  intro j
  filter_upwards [sourceSamplingSquaredError_ae (r j) (b j) (a j) (c j) (a' j) (c' j),
    sourceSamplingEmpiricalDensity_uniform (r j) (b j) (a j) (c j) (a' j) (c' j)] with θ he hu
  exact ⟨he.2,hu⟩

end
end FiniteFactor

end OAI
