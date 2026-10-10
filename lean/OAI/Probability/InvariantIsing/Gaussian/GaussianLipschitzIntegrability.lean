import OAI.Probability.InvariantIsing.Haar.PublishedInputs
import Mathlib.Probability.Distributions.Gaussian.Fernique

namespace OAI

/-! Square integrability of the actual Lipschitz observables in the Gaussian input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InvariantIsing

lemma gaussian_lipschitz_memLp_two {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hi : MemLp (fun x : EuclideanSpace ℝ (Fin d) => x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := IsGaussian.memLp_id _ 2 (by norm_num)
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hh := (hc.comp_memLp (by simp) hi).add
    (memLp_const (f 0) : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => f 0) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))))
  convert hh using 1
  funext x
  simp

lemma gaussian_lipschitz_integrable {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (gaussian_lipschitz_memLp_two hf).integrable (by norm_num)

end InvariantIsing

end

end OAI
