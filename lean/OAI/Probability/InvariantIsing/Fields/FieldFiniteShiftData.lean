import OAI.Probability.InvariantIsing.Fields.FieldFiniteShift

namespace OAI

/-! The joint gradient and Hessian of an affine-noise scalar payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteLinear_add {n : ℕ} (A B : Fin n → ℝ) (a b : ℝ) :
    fieldFiniteLinear A a + fieldFiniteLinear B b =
      fieldFiniteLinear (fun i => A i + B i) (a + b) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [add_apply, fieldFiniteLinear_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma fieldFiniteLinear_smul {n : ℕ} (c : ℝ) (A : Fin n → ℝ) (a : ℝ) :
    c • fieldFiniteLinear A a = fieldFiniteLinear (fun i => c * A i) (c * a) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [smul_apply, fieldFiniteLinear_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def shiftPoint (_F : FieldFiniteFamily n I) (a : ℝ) (v : Fin n → ℝ) (u : ℝ) (p : FieldCovariate n) : FieldCovariate n :=
  (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u)

def shiftedMean (a : ℝ) (v : Fin n → ℝ) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.X (F.shiftPoint a v u p)

def shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.P i (F.shiftPoint a v u p) + F.X (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u)

def shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.PX i (F.shiftPoint a v u p) + F.XX (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u)

def shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.PP i j (F.shiftPoint a v u p) +
    F.PX i (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 j * u) +
    F.PX j (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u) +
    F.XX (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u) * (fieldFiniteSlope a v p.1 j * u) +
    F.X (F.shiftPoint a v u p) * (fieldFiniteCurvature a v p.1 i j * u)

lemma shiftedMean_hasFDerivAt (a : ℝ) (v : Fin n → ℝ) (u : ℝ) {p : FieldCovariate n}
    (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (F.shiftedMean a v u)
      (fieldFiniteLinear (fun i => F.shiftedMixed a v i u p) (F.XX (F.shiftPoint a v u p))) p :=
  field_finite_affine_shift_hasFDerivAt F.derivativeX a v u hp hv

lemma shiftedTangent_hasFDerivAt (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (F.shiftedTangent a v i u)
      (fieldFiniteLinear (fun j => F.shiftedHessian a v i j u p)
        (F.shiftedMixed a v i u p)) p := by
  have hP := field_finite_affine_shift_hasFDerivAt (F.derivativeP i) a v u hp hv
  have hX := F.shiftedMean_hasFDerivAt a v u hp hv
  have hc := (fieldFiniteSlope_hasFDerivAt a v i hv).mul_const u
  have h := hP.add (hX.mul hc)
  convert h using 1
  · rfl
  · simp only [fieldFiniteLinear_smul, fieldFiniteLinear_add]
    congr 1
    · funext j
      dsimp only [shiftedHessian, shiftedMixed, shiftedMean, shiftPoint]
      ring
    · dsimp only [shiftedMixed, shiftedMean, shiftPoint]
      ring

lemma shiftedHessian_symmetric (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    F.shiftedHessian a v i j u p = F.shiftedHessian a v j i u p := by
  unfold shiftedHessian
  rw [F.symmetric i j (F.shiftPoint a v u p) hp, fieldFiniteCurvature_symmetric a v p.1 i j]
  ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
