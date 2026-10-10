import Mathlib
import OAI.Probability.SKRatio.Matrices.MatrixCoordinates

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma gaussianCoordinate_memLp (a : MatrixCoordinates ι) :
    MemLp (fun g : MatrixCoordinates ι → ℝ => g a) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  exact (IsGaussian.memLp_id (gaussianReal 0 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : MatrixCoordinates ι => gaussianReal 0 1) a)

lemma gaussianCoordinate_integral_sq (a : MatrixCoordinates ι) :
    (∫ g : MatrixCoordinates ι → ℝ, (g a)^2 ∂Measure.pi (fun _ => gaussianReal 0 1)) = 1 := by
  rw [integral_comp_eval (μ := fun _ : MatrixCoordinates ι => gaussianReal 0 1) (i := a) (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 1))]
  have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at hh
  simpa only [sub_zero,NNReal.coe_one] using hh

lemma goeEntry_memLp (r : ℝ) (i b : ι) :
    MemLp (fun g => goeMatrix r g i b) 2
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  exact ((gaussianCoordinate_memLp (.inl (i,b))).add
    (gaussianCoordinate_memLp (.inl (b,i)))).const_mul _

lemma goeEntry_integral_sq_le {r : ℝ} (hr : 0 ≤ r) (i b : ι) :
    (∫ g, (goeMatrix r g i b)^2
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤ 2*r := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  have h1 := (gaussianCoordinate_memLp (.inl (i,b))).integrable_sq
  have h2 := (gaussianCoordinate_memLp (.inl (b,i))).integrable_sq
  have hb (g : MatrixCoordinates ι → ℝ) : (goeMatrix r g i b)^2 ≤
      r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
    have hx : (g (.inl (i,b))+g (.inl (b,i)))^2 ≤
        2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
      nlinarith only [sq_nonneg (g (.inl (i,b))-g (.inl (b,i)))]
    simp only [goeMatrix,mul_pow]
    calc
      _ ≤ (sqrt (2*r)/2)^2*(2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2)) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = _ := by rw [div_pow,sq_sqrt (by positivity)]; ring
  calc
    _ ≤ ∫ g, r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) ∂μ :=
      integral_mono (goeEntry_memLp r i b).integrable_sq ((h1.add h2).const_mul r) hb
    _ = 2*r := by
      rw [integral_const_mul,integral_add h1 h2,gaussianCoordinate_integral_sq,
        gaussianCoordinate_integral_sq]
      ring

end SKRatioGaussian

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
