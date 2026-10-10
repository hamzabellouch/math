import OAI.Probability.InvariantIsing.Gaussian.GaussianGramColumns
import Mathlib.Probability.ProductMeasure

namespace OAI

/-! The physical Gaussian matrix as independent Gaussian columns. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

def gaussianColumnArray {N m : ℕ} (g : Fin m → Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 (fun p => g p.2 p.1)

lemma gaussianColumnArray_hasLaw (N m : ℕ) :
    HasLaw (gaussianColumnArray (N := N) (m := m)) (stdGaussian _)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  let μ := gaussianReal 0 1
  have hc : HasLaw (MeasurableEquiv.curry (Fin m) (Fin N) ℝ).symm
      (Measure.pi (fun _ : Fin m × Fin N => μ))
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => μ))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable.aemeasurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry_symm (fun (_ : Fin m) (_ : Fin N) => μ)
  have hs := (measurePreserving_piCongrLeft (fun _ : Fin N × Fin m => μ)
    (Equiv.prodComm (Fin m) (Fin N))).hasLaw
  have hz : HasLaw (WithLp.toLp 2 : (Fin N × Fin m → ℝ) → EuclideanSpace ℝ (Fin N × Fin m))
      (stdGaussian _) (Measure.pi (fun _ : Fin N × Fin m => μ)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  convert hz.comp (hs.comp hc) using 1
  rfl

lemma gaussianColumnArray_column {N m : ℕ} (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramRawColumn (gaussianColumnArray g) j = g j := rfl

end InvariantIsing

end

end OAI
