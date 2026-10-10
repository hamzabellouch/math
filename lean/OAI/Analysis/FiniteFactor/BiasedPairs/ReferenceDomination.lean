import OAI.Analysis.FiniteFactor.Coupling.FiniteDisintegration
import OAI.Analysis.FiniteFactor.BiasedPairs.PrefixLimit

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

def sourceDiagonalHaarKernel : Kernel ℝ ℝ where
  toFun := diagonalHaarReference
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [diagonalHaarReference,Measure.smul_apply,Measure.add_apply,smul_eq_mul]
    exact measurable_const.mul (((Measure.measurable_coe hS).comp Measure.measurable_dirac).add measurable_const)

instance sourceDiagonalHaarKernel_markov : IsMarkovKernel sourceDiagonalHaarKernel :=
  ⟨fun t => diagonalHaarReference_probability t⟩

/-- Independent diagonal-or-Haar replacement at a finite set of coordinates. -/
def sourceFiniteReferenceKernel (F : Finset SourceCoordinate) :
    Kernel (SourceCoordinate → ℝ) (SourceCoordinate → ℝ) := by
  letI : ∀ i, IsMarkovKernel (if i ∈ F then sourceDiagonalHaarKernel else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i => if i ∈ F then sourceDiagonalHaarKernel else Kernel.id)

instance sourceFiniteReferenceKernel_markov (F : Finset SourceCoordinate) :
    IsMarkovKernel (sourceFiniteReferenceKernel F) := by
  unfold sourceFiniteReferenceKernel
  infer_instance

/-- The mixed prefix posterior is dominated for every full conditioning vector. -/
theorem sourceMixedPosterior_ac (j : ℕ) (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    mixedPosteriorKernel (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
      (fun i => decide (i ∈ F)) x ≪ sourceFiniteReferenceKernel F x := by
  have hh := vectorPosterior_finite_ac
    (fun i : SourceCoordinate => stagedCouplingParameters j i.1) F x
  rw [vectorPosterior_finite_map] at hh
  convert hh using 1 <;>
    dsimp [mixedPosteriorKernel,sourceFiniteReferenceKernel,independentKernel] <;>
    congr 1 <;> funext i <;> by_cases hi : i ∈ F <;>
      simp [hi,sourceDiagonalHaarKernel] <;> rfl

/-- Actual prefix-pair domination after integrating the full x marginal.
The x marginal is replaced by Haar only through its proved density, so the
infinite diagonal tail is not assumed Haar-distributed. -/
theorem sourceBiasedPrefix_ac_reference (j n : ℕ) :
    sourceBiasedRealMeasure j (sourceBiasedPrefixMask n) ≪
      sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel (blockPrefix sourceBlockSize n) := by
  let p := fun i : SourceCoordinate => stagedCouplingParameters j i.1
  have he : (fun i : SourceCoordinate => decide (i ∈ blockPrefix sourceBlockSize n)) =
      sourceBiasedPrefixMask n := by
    funext i
    simp [sourceBiasedPrefixMask,mem_blockPrefix]
  have hdis := mixedPosterior_disintegration p (sourceBiasedPrefixMask n)
  have hbase : (vectorCoupling p).map (vectorEndpoint (fun _ => false)) ≪ sourceSamplingHaar := by
    obtain ⟨g,_,_,_,hg,_⟩ := sourceBiasedEndpoint_density j (fun _ => false)
    change (sourceBiasedLaw j).map (sourceBiasedEndpoint (fun _ => false)) ≪ sourceSamplingHaar
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hcond : ∀ᵐ x ∂((vectorCoupling p).map (vectorEndpoint (fun _ => false))),
      mixedPosteriorKernel p (sourceBiasedPrefixMask n) x ≪
        sourceFiniteReferenceKernel (blockPrefix sourceBlockSize n) x := by
    apply Filter.Eventually.of_forall
    intro x
    rw [← he]
    exact sourceMixedPosterior_ac j _ x
  have hh := hbase.compProd hcond
  rw [hdis] at hh
  exact hh

end
end FiniteFactor

end OAI
