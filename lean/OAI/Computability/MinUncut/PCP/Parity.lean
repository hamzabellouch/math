import Mathlib
import OAI.Computability.MinUncut.Estimates.Convolution
import OAI.Computability.MinUncut.Estimates.ArraySum

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma H_neg (d : ℕ) (x : ℝ) : H d (-x) = (-1 : ℝ)^d * H d x := by
  have hh := H_noise (-1) 0 x (by norm_num) d
  simpa [γ] using hh

lemma H_sign (d : ℕ) (k : BinaryFourier.F₂) (x : ℝ) :
    H d (BinaryFourier.sign k*x) = BinaryFourier.sign (k*(d : BinaryFourier.F₂))*H d x := by
  have hs : BinaryFourier.sign (d : BinaryFourier.F₂) = (-1 : ℝ)^d := by
    induction d with
    | zero => simp
    | succ d ih => simp [Nat.cast_add, BinaryFourier.sign_add, ih, pow_succ]
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : k = 1 := by
      have h : ∀ a : BinaryFourier.F₂, a = 0 ∨ a=1 := by decide
      exact (h k).resolve_left hk
    simp only [hk1, BinaryFourier.sign_one, neg_one_mul, one_mul, H_neg, hs]

variable {ι : Type*} [Fintype ι]

def parity (k : ι → BinaryFourier.F₂) (a : ι → ℕ) : BinaryFourier.F₂ := ∑ i, k i * (a i : BinaryFourier.F₂)

lemma psi_diagonal (k : ι → BinaryFourier.F₂) (a : ι → ℕ) (c : ι → ℝ) :
    psi a (Inner.diagonal k c) = BinaryFourier.sign (parity k a) * psi a c := by
  simp only [psi, Inner.diagonal, H_sign, Finset.prod_mul_distrib, parity, RowNoise.sign_sum]

lemma coeff_diagonal (k : ι → BinaryFourier.F₂) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (fun c => f (Inner.diagonal k c)) a = BinaryFourier.sign (parity k a)*coeff f a := by
  unfold coeff
  change (∫ c, psi a c * f (Inner.diagonal k c) ∂Inner.gauss ι) =
    BinaryFourier.sign (parity k a)*(∫ c, psi a c*f c ∂Inner.gauss ι)
  rw [← Inner.integral_diagonal k (fun c => psi a c * f (Inner.diagonal k c))]
  simp only [Inner.diagonal_involutive k _, psi_diagonal, mul_assoc, integral_const_mul]

end MinUncut.GaussianHermite

end

end OAI
