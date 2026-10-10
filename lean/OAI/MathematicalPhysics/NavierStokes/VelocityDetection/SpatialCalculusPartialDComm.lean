import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.SpatialCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff

theorem partialD_comm {n : ℕ} {f : Coord n → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin n) (X : Coord n) :
    partialD i (partialD j f) X = partialD j (partialD i f) X := by
  have heq (k : Fin n) : partialD k f = fun Y => fderiv ℝ f Y (Pi.single k 1) :=
    funext (partialD_eq_fderiv k (hf.differentiable (by norm_num)))
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have hij (a b : Fin n) : partialD a (partialD b f) X =
      fderiv ℝ (fderiv ℝ f) X (Pi.single a 1) (Pi.single b 1) := by
    rw [partialD_eq_fderiv a ((contDiff_partialD b hf).differentiable (by norm_num)), heq b]
    rw [fderiv_clm_apply (hd X) (differentiableAt_const _)]
    simp
  rw [hij, hij]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq _ _

theorem partialD_neg {n : ℕ} (i : Fin n) (f : Coord n → ℝ) (X : Coord n) :
    partialD i (-f) X = -partialD i f X := by
  simp [partialD, spatialD]

def rotatedGradient (ψ : Coord 2 → ℝ) (X : Coord 2) : Coord 2 :=
  ![partialD 1 ψ X, -partialD 0 ψ X]

theorem divergence_rotatedGradient {ψ : Coord 2 → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (X : Coord 2) :
    divergence (fun _ => rotatedGradient ψ) 0 X = 0 := by
  simp only [divergence, Fin.sum_univ_two, rotatedGradient, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change partialD 0 (partialD 1 ψ) X + partialD 1 (-partialD 0 ψ) X = 0
  rw [partialD_neg, partialD_comm hψ 0 1]
  ring

end VelocityDetection.SpatialCalculus
end

end OAI
