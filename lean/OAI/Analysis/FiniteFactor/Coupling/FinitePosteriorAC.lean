import OAI.Analysis.FiniteFactor.FiniteProductAbsoluteContinuity
import OAI.Analysis.FiniteFactor.Coupling.VectorBayes

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- A normalized reference law allowing either a diagonal or a Haar draw. -/
def diagonalHaarReference (t : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac t + unitIntervalMeasure)

instance diagonalHaarReference_probability (t : ℝ) :
    IsProbabilityMeasure (diagonalHaarReference t) := by
  constructor
  simpa [diagonalHaarReference,Measure.smul_apply,Measure.add_apply,measure_univ] using ENNReal.inv_two_add_inv_two

/-- Every coordinate posterior has an absolutely continuous off-diagonal part.
The diagonal atom is retained explicitly in the reference measure. -/
theorem posteriorKernel_ac_diagonalHaar (p : CouplingParameters) (right : Bool) (t : ℝ) :
    p.posteriorKernel right t ≪ diagonalHaarReference t := by
  apply Measure.AbsolutelyContinuous.smul_right _ (by norm_num)
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hzero
  have hz : Measure.dirac t S = 0 ∧ unitIntervalMeasure S = 0 := by
    simpa only [Measure.add_apply,add_eq_zero] using hzero
  have hc (i : Fin 5) : p.endpointComponentLaw (!right) i S = 0 :=
    withDensity_absolutelyContinuous _ _ hz.2
  change p.posteriorLaw right t S = 0
  simp [posteriorLaw,Measure.add_apply,Measure.finsetSum_apply,Measure.smul_apply,hz.1,hc]

/-- Full conditional law with only F resampled, given the entire original
endpoint vector. The coordinates outside F are exactly fixed. -/
theorem vectorPosterior_finite_map {ι : Type*} [DecidableEq ι]
    (p : ι → CouplingParameters) (F : Finset ι) (x : ι → ℝ) :
    (vectorPosterior p (fun _ => false) x).map
      (fun y i => if i ∈ F then y i else x i) =
      Measure.infinitePi (fun i => if i ∈ F then (p i).posteriorKernel false (x i)
        else Measure.dirac (x i)) := by
  change (Measure.infinitePi (fun i => (p i).posteriorKernel false (x i))).map _ = _
  rw [Measure.infinitePi_map_pi _ (f := fun i y => if i ∈ F then y else x i)
    (fun i => by split_ifs <;> fun_prop)]
  congr 1
  funext i
  by_cases hi : i ∈ F
  · simp [hi]
  · simp [hi,Measure.map_const]

/-- Absolute continuity of the actual full-vector conditional law after a
finite replacement. This uses finitely many coordinate changes only. -/
theorem vectorPosterior_finite_ac {ι : Type*} [DecidableEq ι]
    (p : ι → CouplingParameters) (F : Finset ι) (x : ι → ℝ) :
    (vectorPosterior p (fun _ => false) x).map
      (fun y i => if i ∈ F then y i else x i) ≪
      Measure.infinitePi (fun i => if i ∈ F then diagonalHaarReference (x i)
        else Measure.dirac (x i)) := by
  rw [vectorPosterior_finite_map]
  let μ := fun i => if i ∈ F then diagonalHaarReference (x i) else Measure.dirac (x i)
  let ν := fun i => if i ∈ F then (p i).posteriorKernel false (x i) else Measure.dirac (x i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => by dsimp [μ]; split_ifs <;> infer_instance
  let : ∀ i, IsProbabilityMeasure (ν i) := fun i => by dsimp [ν]; split_ifs <;> infer_instance
  apply infinitePi_ac_of_finite_changes μ ν F
  · intro i hi
    simpa [μ,ν,hi] using (p i).posteriorKernel_ac_diagonalHaar false (x i)
  · intro i hi
    simp [μ,ν,hi]

end CouplingParameters
end
end FiniteFactor

end OAI
