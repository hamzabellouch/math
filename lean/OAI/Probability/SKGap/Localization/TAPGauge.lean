import Mathlib
import OAI.Probability.SKGap.Stability.RootDiagonalTransfer

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

def spinAct {n : ℕ} (s : Spin n) (y : Field n) : Field n :=
  fun i=>spinValue (s i)*y i

def spinMatrixAct {n : ℕ} (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i k=>spinValue (s i)*J i k*spinValue (s k)

lemma spinAct_involutive {n : ℕ} (s : Spin n) (y : Field n) : spinAct s (spinAct s y)=y := by
  ext i
  simp only [spinAct,← mul_assoc,← sq,spinValue_sq,one_mul]

lemma spinAct_tanh {n : ℕ} (s : Spin n) (y : Field n) :
    magnetization (spinAct s y)=spinAct s (magnetization y) := by
  ext i
  cases h : s i <;> simp [magnetization,spinAct,spinValue,h,tanh_neg]

lemma spinAct_overlap {n : ℕ} (s : Spin n) (y : Field n) : overlap (spinAct s y)=overlap y := by
  unfold overlap
  rw [spinAct_tanh]
  simp only [spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_variance {n : ℕ} (s : Spin n) (y : Field n) :
    spinVariance (spinAct s y)=spinVariance y := by
  ext i
  simp only [spinVariance,spinAct_tanh,spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_sqnorm {n : ℕ} (s : Spin n) (y : Field n) : vectorSqNorm (spinAct s y)=vectorSqNorm y := by
  simp only [vectorSqNorm,spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_norm {n : ℕ} (s : Spin n) (y : Field n) : vectorNorm (spinAct s y)=vectorNorm y := by
  have hh : vectorNorm (spinAct s y)^2=vectorNorm y^2 := by
    rw [vectorNorm_sq,vectorNorm_sq,spinAct_sqnorm]
  nlinarith only [hh,vectorNorm_nonneg (spinAct s y),vectorNorm_nonneg y]

lemma spinAct_quadratic {n : ℕ} (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n) :
    quadraticForm (spinMatrixAct s J) (spinAct s y)=quadraticForm J y := by
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [spinMatrixAct,spinAct]
  calc
    _ = spinValue (s i)^2*spinValue (s k)^2*(y i*J i k*y k) := by ring
    _ = _ := by rw [spinValue_sq,spinValue_sq,one_mul,one_mul]

lemma spinAct_tap {n : ℕ} (s : Spin n) (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    tapField j (spinMatrixAct s J) (spinAct s h) (spinAct s y)=spinAct s (tapField j J h y) := by
  ext i
  simp only [tapField,spinAct_tanh,onsager,spinAct_overlap,spinAct,spinMatrixAct]
  have hs : (∑ k, spinValue (s i)*J i k*spinValue (s k)*(spinValue (s k)*magnetization y k))=
      spinValue (s i)*∑ k,J i k*magnetization y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = spinValue (s i)*(J i k*magnetization y k)*spinValue (s k)^2 := by ring
      _ = _ := by rw [spinValue_sq,mul_one]
  rw [hs]
  ring

lemma spinAct_hessian {n : ℕ} (s : Spin n) (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y a : Field n) :
    fieldHessian j (spinMatrixAct s J) (spinAct s y) a=spinMatrixAct s (fieldHessian j J y a) := by
  ext i k
  simp only [fieldHessian,hessianCore,onsager,spinAct_overlap,spinAct_tanh,spinAct,spinMatrixAct]
  by_cases hik : i=k
  · subst k
    cases hi : s i <;> simp [spinValue]
  · simp only [ite_eq_right hik]
    ring

lemma spinAct_bad {n : ℕ} (s : Spin n) (j A ε c ρ : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h → rootBad j A ε c ρ (spinMatrixAct s J) (spinAct s h) := by
  rintro ⟨y,hy,a,ha,hd,x,hx,hq⟩
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (spinAct s x.ofLp)
  have hz : ‖z‖=1 := by
    change vectorNorm (spinAct s x.ofLp)=1
    rw [spinAct_norm]
    exact hx
  refine ⟨spinAct s y,?_,a,ha,?_,z,hz,?_⟩
  · rw [spinAct_tap,spinAct_norm]
    exact hy
  · rw [spinAct_variance]
    exact hd
  · rw [spinAct_hessian]
    exact (spinAct_quadratic s (fieldHessian j J y a) x.ofLp).trans_le hq
end SKGap
end
end

end OAI
