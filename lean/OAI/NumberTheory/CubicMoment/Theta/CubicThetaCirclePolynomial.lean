import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

/-! The finite Fourier polynomial underlying higher angular extraction.
Its highest Fourier mode is a pure power of the complex frequency. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def cubicThetaCirclePower (w : ℂ) (m : ℕ) (t : AddCircle (1:ℝ)) : ℂ :=
  (w*fourier 1 t+star w*fourier (-1) t)^m

lemma cubicThetaCircle_fourier_pow (j : ℤ) (m : ℕ) (t : AddCircle (1:ℝ)) :
    (fourier j t)^m=fourier ((m:ℤ)*j) t := by
  induction m with
  | zero => simp
  | succ m hm =>
      rw [pow_succ,hm,show ((m+1:ℕ):ℤ)*j=(m:ℤ)*j+j by push_cast; ring,fourier_add]

lemma cubicThetaCirclePower_expansion (w : ℂ) (m : ℕ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePower w m t=
      ∑ j∈Finset.range (m+1),
        ((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j)*fourier (2*(j:ℤ)-(m:ℤ)) t := by
  unfold cubicThetaCirclePower
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j≤m := by have := Finset.mem_range.mp hj; omega
  rw [mul_pow,mul_pow,cubicThetaCircle_fourier_pow,cubicThetaCircle_fourier_pow]
  simp only [mul_one,mul_neg_one]
  have he : (j:ℤ)+(-((m-j:ℕ):ℤ))=2*(j:ℤ)-(m:ℤ) := by omega
  calc
    _ = (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*
        (fourier (j:ℤ) t*fourier (-((m-j:ℕ):ℤ)) t) := by ring
    _ = _ := by rw [←fourier_add,he]

lemma cubicThetaCirclePower_coefficient (w : ℂ) (m : ℕ) (k : ℤ) :
    fourierCoeff (cubicThetaCirclePower w m) k=
      ∑ j∈Finset.range (m+1),
        ((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j)*
          (if k=2*(j:ℤ)-(m:ℤ) then 1 else 0) := by
  have he : cubicThetaCirclePower w m=
      ∑ j∈Finset.range (m+1),fun t : AddCircle (1:ℝ) =>
        (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*fourier (2*(j:ℤ)-(m:ℤ)) t := by
    funext t
    simpa only [Finset.sum_apply] using cubicThetaCirclePower_expansion w m t
  rw [he]
  have hi (j : ℕ) (_ : j∈Finset.range (m+1)) : Integrable
      (fun t : AddCircle (1:ℝ) => (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*
        fourier (2*(j:ℤ)-(m:ℤ)) t) AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier _).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [fourierCoeff.sum _ _ hi]
  simp only [Finset.sum_apply,fourierCoeff.const_mul,fourierCoeff_fourier,Pi.single_apply]

lemma cubicThetaCirclePower_coefficient_above (w : ℂ) {m k : ℕ} (hmk : m<k) :
    fourierCoeff (cubicThetaCirclePower w m) (k:ℤ)=0 := by
  rw [cubicThetaCirclePower_coefficient]
  apply Finset.sum_eq_zero
  intro j hj
  have hjm : j≤m := by have := Finset.mem_range.mp hj; omega
  have he : (k:ℤ)≠2*(j:ℤ)-(m:ℤ) := by omega
  simp only [he,ite_false,mul_zero]

lemma cubicThetaCirclePower_coefficient_top (w : ℂ) (m : ℕ) :
    fourierCoeff (cubicThetaCirclePower w m) (m:ℤ)=w^m := by
  rw [cubicThetaCirclePower_coefficient]
  rw [Finset.sum_eq_single m]
  · have he : (m:ℤ)=2*(m:ℤ)-(m:ℤ) := by ring
    rw [ite_eq_left he]
    simp
  · intro j hj hjm
    have he : (m:ℤ)≠2*(j:ℤ)-(m:ℤ) := by omega
    simp only [he,ite_false,mul_zero]
  · simp

end CubicFirstMoment

end

end OAI
