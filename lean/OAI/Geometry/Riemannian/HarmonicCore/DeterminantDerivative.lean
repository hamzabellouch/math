import OAI.Geometry.Riemannian.HarmonicCore.Model

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main

lemma determinant_hasDerivAt {G : ℝ → M3} {D : M3} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (D i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (((G t).adjugate * D).trace) t := by
  have hd := (((((h 0 0).fun_mul (h 1 1)).fun_mul (h 2 2)).sub
    (((h 0 0).fun_mul (h 1 2)).fun_mul (h 2 1))).sub
    (((h 0 1).fun_mul (h 1 0)).fun_mul (h 2 2))).add
    (((h 0 1).fun_mul (h 1 2)).fun_mul (h 2 0))
  have hd := (hd.add (((h 0 2).fun_mul (h 1 0)).fun_mul (h 2 1))).sub
    (((h 0 2).fun_mul (h 1 1)).fun_mul (h 2 0))
  convert! hd using 1
  · funext s
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.det_fin_three]
  · simp [Matrix.trace, Fin.sum_univ_three,
      Matrix.adjugate_fin_three, Matrix.vecMul, dotProduct]
    ring

end HarmonicCounterexample.Main

end

end OAI
