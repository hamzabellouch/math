import Mathlib
import OAI.Analysis.AffineBernstein.MatrixMetric
import OAI.Analysis.AffineBernstein.FlatFCalculus
import OAI.Analysis.AffineBernstein.JointTubeMetrics

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma flatInversePair_eq_matrixPair {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Matrix ι ι ℝ) (v : ι → V) (f g : V → ℝ) (x : V) :
    flatInversePair A v f g x = inverseMatrixPair A (fun i => dirDeriv (v i) f x) (fun i => dirDeriv (v i) g x) := rfl

lemma flatInversePair_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : ι → E) (f : E → ℝ) (x : E) :
    0 ≤ flatInversePair A v f f x := inverseMatrixPair_self_nonneg hA _

lemma tubeBasePair_nonneg {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hh : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef) (f : S × E → ℝ) :
    0 ≤ tubeBasePair H b f f q := mul_nonneg hh (inverseMatrixPair_self_nonneg hB _)

lemma tubeBasePair_cauchy {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix H q b).PosDef) (f g : S × E → ℝ) :
    tubeBasePair H b f g q^2 ≤ tubeBasePair H b f f q*tubeBasePair H b g g q := by
  have hc := mul_le_mul_of_nonneg_left (inverseMatrixPair_cauchy hB
    (fun i => dirDeriv (b i,(0:E)) f q) (fun i => dirDeriv (b i,(0:E)) g q)) (sq_nonneg (H q))
  change H q^2 * (flatInversePair _ _ f g q)^2 ≤ H q^2 *
    (flatInversePair _ _ f f q * flatInversePair _ _ g g q) at hc
  unfold tubeBasePair
  nlinarith [hc]

lemma tubeBasePair_symm {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix H q b).PosDef) (f g : S × E → ℝ) :
    tubeBasePair H b f g q = tubeBasePair H b g f q := by
  unfold tubeBasePair
  rw [flatInversePair_symm _ (by simpa only [Matrix.isHermitian_iff_isSymm] using hB.isHermitian)]

lemma tubeBasePair_add_self {H f g : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) (hB : (tubeBaseMatrix H q b).PosDef) :
    tubeBasePair H b (fun y => f y+g y) (fun y => f y+g y) q =
      tubeBasePair H b f f q+2*tubeBasePair H b f g q+tubeBasePair H b g g q := by
  have hv (v : S × E) : dirDeriv v (fun y => f y+g y) q = dirDeriv v f q+dirDeriv v g q := by
    simp only [dirDeriv,fderiv_fun_add hf hg,add_apply]
  simp only [tubeBasePair,flatInversePair_eq_matrixPair,hv]
  rw [inverseMatrixPair_add_left,inverseMatrixPair_add_right,inverseMatrixPair_add_right,
    inverseMatrixPair_symm (by simpa only [Matrix.isHermitian_iff_isSymm] using hB.isHermitian)
      (fun i => dirDeriv (b i,0) g q) (fun i => dirDeriv (b i,0) f q)]
  ring

end AffineBernstein
end

end OAI
