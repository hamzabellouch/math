import Mathlib
import OAI.Analysis.WeakInfiniteness.OInfinityUniversal

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

lemma cstar_norm_one_le_one : ‖(1:A)‖≤1 := by
  have hh : ‖star (1:A)*(1:A)‖=‖(1:A)‖*‖(1:A)‖ := CStarRing.norm_star_mul_self
  simp only [star_one,mul_one] at hh
  nlinarith [norm_nonneg (1:A)]

lemma norm_isometry_le_one {s : A} (hs : star s*s=1) : ‖s‖≤1 := by
  have hh : ‖star s*s‖=‖s‖*‖s‖ := CStarRing.norm_star_mul_self
  rw [hs] at hh
  have hn : ‖(1:A)‖≤1 := cstar_norm_one_le_one
  have hp := norm_nonneg s
  nlinarith

lemma norm_cuntzWord_le_one (s : ℕ → A) (hs : ∀ i,‖s i‖≤1) (w : List (ℕ × Bool)) :
    ‖cuntzWord s w‖≤1 := by
  induction w with
  | nil => exact cstar_norm_one_le_one
  | cons ib w ih =>
    rcases ib with ⟨i,b⟩
    have hx : ‖if b then s i else star (s i)‖≤1 := by cases b <;> simpa using hs i
    exact (norm_mul_le _ _).trans ((mul_le_mul hx ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

lemma norm_commutator_star_right (a x : A) :
    ‖a*star x-star x*a‖=‖star a*x-x*star a‖ := by
  rw [← norm_star (a*star x-star x*a),star_sub,star_mul,star_mul,star_star,norm_sub_rev]

lemma norm_commutator_mul_le (a x y : A) :
    ‖a*(x*y)-(x*y)*a‖≤‖a*x-x*a‖*‖y‖+‖x‖*‖a*y-y*a‖ := by
  have he : a*(x*y)-(x*y)*a=(a*x-x*a)*y+x*(a*y-y*a) := by noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

lemma norm_cuntzWord_commutator_le (s : ℕ → A) (hs : ∀ i,‖s i‖≤1)
    (a : A) (w : List (ℕ × Bool)) (δ : ℝ) (hδ : 0≤δ)
    (hcomm : ∀ ib ∈ w,‖a*s ib.1-s ib.1*a‖≤δ ∧ ‖star a*s ib.1-s ib.1*star a‖≤δ) :
    ‖a*cuntzWord s w-cuntzWord s w*a‖≤(w.length:ℝ)*δ := by
  induction w with
  | nil => simp [cuntzWord]
  | cons ib w ih =>
    rcases ib with ⟨i,b⟩
    have hx : ‖if b then s i else star (s i)‖≤1 := by cases b <;> simpa using hs i
    have hc : ‖a*(if b then s i else star (s i))-(if b then s i else star (s i))*a‖≤δ := by
      have hh := hcomm (i,b) (by simp)
      cases b
      · simpa only [Bool.false_eq_true,↓reduceIte,norm_commutator_star_right] using hh.2
      · simpa using hh.1
    have hi := ih (fun p hp => hcomm p (List.mem_cons_of_mem _ hp))
    have hn := norm_cuntzWord_le_one s hs w
    change ‖a*((if b then s i else star (s i))*cuntzWord s w)-
      ((if b then s i else star (s i))*cuntzWord s w)*a‖≤_
    calc
      _ ≤ ‖a*(if b then s i else star (s i))-(if b then s i else star (s i))*a‖*‖cuntzWord s w‖+
          ‖if b then s i else star (s i)‖*‖a*cuntzWord s w-cuntzWord s w*a‖ := norm_commutator_mul_le _ _ _
      _ ≤ δ*1+1*((w.length:ℝ)*δ) := by
        apply add_le_add
        · exact mul_le_mul hc hn (norm_nonneg _) hδ
        · exact mul_le_mul hx hi (norm_nonneg _) zero_le_one
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

def cuntzPolynomialCentralWeight (c : List (ℕ × Bool) →₀ ℂ) : ℝ :=
  ∑ w ∈ c.support,‖c w‖*(w.length:ℝ)

lemma cuntzPolynomialCentralWeight_nonneg (c : List (ℕ × Bool) →₀ ℂ) :
    0≤cuntzPolynomialCentralWeight c := by
  unfold cuntzPolynomialCentralWeight
  positivity

lemma norm_cuntzPolynomial_commutator_le (s : ℕ → A) (hs : ∀ i,‖s i‖≤1)
    (a : A) (c : List (ℕ × Bool) →₀ ℂ) (δ : ℝ) (hδ : 0≤δ)
    (hcomm : ∀ w ∈ c.support,∀ ib ∈ w,
      ‖a*s ib.1-s ib.1*a‖≤δ ∧ ‖star a*s ib.1-s ib.1*star a‖≤δ) :
    ‖a*cuntzPolynomial s c-cuntzPolynomial s c*a‖≤cuntzPolynomialCentralWeight c*δ := by
  have he : a*cuntzPolynomial s c-cuntzPolynomial s c*a=
      ∑ w ∈ c.support,c w • (a*cuntzWord s w-cuntzWord s w*a) := by
    simp only [cuntzPolynomial,Finsupp.sum,Finset.mul_sum,Finset.sum_mul,
      ← Finset.sum_sub_distrib,mul_smul_comm,smul_mul_assoc,smul_sub]
  rw [he]
  calc
    _ ≤ ∑ w ∈ c.support,‖c w • (a*cuntzWord s w-cuntzWord s w*a)‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ c.support,‖c w‖*((w.length:ℝ)*δ) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_cuntzWord_commutator_le s hs a w δ hδ (hcomm w hw)) (norm_nonneg _)
    _ = _ := by simp only [cuntzPolynomialCentralWeight,Finset.sum_mul,mul_assoc]

end

end WeakPureInfiniteness
end

end OAI
