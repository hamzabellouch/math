import OAI.Analysis.FiniteFactor.OrbitSampling.TestedMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.FirstMarginal

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- A finite rational cylinder test, with two closed intervals per tested
coordinate. Whole-circle tests fill the remaining coordinates. -/
abbrev SourceSamplingRationalTest :=
  Σ K : Finset SourceCoordinate, K → (ℚ × ℚ) × (ℚ × ℚ)

instance : Countable SourceSamplingRationalTest := inferInstance

def sourceSamplingRationalEndpoints (T : SourceSamplingRationalTest) (i : SourceCoordinate) :
    (ℚ × ℚ) × (ℚ × ℚ) :=
  if hi : i ∈ T.1 then T.2 ⟨i,hi⟩ else ((0,1),(0,1))

def sourceSamplingRationalX (T : SourceSamplingRationalTest) (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceSamplingRationalEndpoints T i).1.1 (sourceSamplingRationalEndpoints T i).1.2

def sourceSamplingRationalY (T : SourceSamplingRationalTest) (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceSamplingRationalEndpoints T i).2.1 (sourceSamplingRationalEndpoints T i).2.2

theorem sourceSamplingRationalTests_outside (T : SourceSamplingRationalTest) (stage : ℕ)
    (hK : T.1 ⊆ sourceSamplingPrefix stage) :
    ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ sourceSamplingRationalX T i ∧
      Set.Ico (0 : ℝ) 1 ⊆ sourceSamplingRationalY T i := by
  intro i hi
  have hnot : i ∉ T.1 := fun h => hi (hK h)
  simp only [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,
    dite_eq_right hnot,Rat.cast_zero,Rat.cast_one]
  exact ⟨Set.Ico_subset_Icc_self,Set.Ico_subset_Icc_self⟩

theorem sourceSamplingPrefix_eventually_covers (K : Finset SourceCoordinate) :
    ∀ᶠ stage : ℕ in atTop, K ⊆ sourceSamplingPrefix stage := by
  filter_upwards [eventually_ge_atTop (K.sup (fun i => i.1))] with stage hstage
  intro i hi
  apply (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mpr
  exact Nat.lt_succ_of_le ((Finset.le_sup (f := fun i => i.1) hi).trans hstage)

/-- A concrete single conull event for every finite I, both orientations, and
all rational cylinder tests. It includes the actual tested measure identity
at every admissible stage, as well as the full-error convergence and L2 bound. -/
theorem sourceSampling_rational_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (r : Bool)
      (T : SourceSamplingRationalTest),
      Tendsto (fun stage => sourceSamplingSquaredError stage r (fun i => decide (i ∈ I))
        (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ) atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ stage,
        MemLp (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ) 2 sourceSamplingHaar ∧
        (∫ x, sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ x ^ 2 ∂sourceSamplingHaar) ≤ C ∧
        (T.1 ⊆ sourceSamplingPrefix stage →
          ((sourceSamplingUntrimmed I stage θ).restrict
            (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).map
              (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
            (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
              (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ x))) := by
  apply ae_all_iff.mpr
  intro I
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro T
  filter_upwards [sourceSamplingSquaredError_ae r (fun i => decide (i ∈ I))
    (fun i => (sourceSamplingRationalEndpoints T i).1.1)
    (fun i => (sourceSamplingRationalEndpoints T i).1.2)
    (fun i => (sourceSamplingRationalEndpoints T i).2.1)
    (fun i => (sourceSamplingRationalEndpoints T i).2.2),
    sourceSamplingEmpiricalDensity_uniform r (fun i => decide (i ∈ I))
    (fun i => (sourceSamplingRationalEndpoints T i).1.1)
    (fun i => (sourceSamplingRationalEndpoints T i).1.2)
    (fun i => (sourceSamplingRationalEndpoints T i).2.1)
    (fun i => (sourceSamplingRationalEndpoints T i).2.2)] with θ he hu
  obtain ⟨C,hC⟩ := hu
  refine ⟨he.2,C,fun stage => ⟨(hC stage).1,(hC stage).2,?_⟩⟩
  intro hK
  exact sourceSamplingUntrimmed_tested_marginal I stage r _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
    (sourceSamplingRationalTests_outside T stage hK) θ

/-- Both actual untested marginal densities are uniformly L2 bounded on one
conull event, simultaneously for all finite I. -/
theorem sourceSampling_both_marginals_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (r : Bool),
      ∃ C : ℝ, ∀ stage, ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  apply ae_all_iff.mpr
  intro I
  apply ae_all_iff.mpr
  intro r
  cases r
  · exact sourceSamplingUntrimmed_first_L2 I
  · exact sourceSamplingUntrimmed_second_L2 I

end
end FiniteFactor

end OAI
