import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexReal

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {m n : ℕ}

lemma multiply_neg (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => -a i j) u = -multiply a u := by
  ext φ i
  simp only [multiply_apply_component,_root_.neg_apply,PiLp.neg_apply,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : SchwartzMap.smulLeftCLM ℂ (-a i j) φ = -SchwartzMap.smulLeftCLM ℂ (a i j) φ := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (-a i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (a i j).hasTemperateGrowth,_root_.neg_apply,neg_smul]
  rw [he,map_neg]
  rfl

lemma multiply_sub (a b : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => a i j-b i j) u = multiply a u-multiply b u := by
  simp only [sub_eq_add_neg,multiply_add,multiply_neg]

def derivativeMatrix (v : D) (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    Fin m → Fin n → 𝓢(D,ℂ) := fun i j => ∂_{v} (a i j)

def squareFirst (e : ι → D) (a : ι → Fin m → Fin n → 𝓢(D,ℂ))
    (b : Fin m → Fin n → 𝓢(D,ℂ)) (c : ι → Fin n → Fin m → 𝓢(D,ℂ))
    (d : Fin n → Fin m → 𝓢(D,ℂ)) (j : ι) : Fin n → Fin n → 𝓢(D,ℂ) :=
  fun k l => matProduct d (a j) k l -
    (∑ i, derivativeMatrix (e i) (matProduct (c i) (a j)) k l) - matProduct (c j) b k l

def squareZero (e : ι → D) (b : Fin m → Fin n → 𝓢(D,ℂ))
    (c : ι → Fin n → Fin m → 𝓢(D,ℂ)) (d : Fin n → Fin m → 𝓢(D,ℂ)) :
    Fin n → Fin n → 𝓢(D,ℂ) :=
  fun k l => matProduct d b k l - ∑ i, derivativeMatrix (e i) (matProduct (c i) b) k l

lemma divergence_square_expansion (e : ι → D) (a : ι → Fin m → Fin n → 𝓢(D,ℂ))
    (b : Fin m → Fin n → 𝓢(D,ℂ)) (c : ι → Fin n → Fin m → 𝓢(D,ℂ))
    (d : Fin n → Fin m → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    -(∑ i, ∂_{e i} (multiply (c i) ((∑ j, multiply (a j) (∂_{e j} u)) + multiply b u))) +
      multiply d ((∑ j, multiply (a j) (∂_{e j} u)) + multiply b u) =
    -(∑ i, ∑ j, multiply (matProduct (c i) (a j)) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e a b c d j) (∂_{e j} u)) + multiply (squareZero e b c d) u := by
  unfold squareFirst squareZero derivativeMatrix
  simp only [map_add,map_sum,multiply_comp,lineDerivOp_add,lineDerivOp_sum,multiply_derivative,
    multiply_sub,multiply_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => multiply (fun k l => ∂_{e i} (matProduct (c i) (a j) k l)) (∂_{e j} u))]
  abel

end TamingCompatibility.ComplexMatrix

end

end OAI
