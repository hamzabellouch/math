import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Exact holding slowdown of finite reversible chains -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X]

def slow (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : FiniteChain X where
  P x y := a*C.P x y+if x=y then 1-a else 0
  π := C.π
  positive := C.positive
  normalized := C.normalized
  nonnegative x y := by
    apply add_nonneg (mul_nonneg ha0 (C.nonnegative x y))
    split_ifs
    · linarith
    · rfl
  stochastic x := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,C.stochastic,mul_one]
    simp
  reversible x y := by
    by_cases h : x=y
    · subst y
      rfl
    · simp only [h,Ne.symm h,ite_false,add_zero]
      nlinarith [C.reversible x y]
  lazy x := by
    simp only [ite_true]
    have hm := mul_le_mul_of_nonneg_left (C.lazy x) ha0
    linarith

lemma stationary (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (slow C a ha0 ha1).π=C.π := rfl

lemma mean (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f : X → ℝ) :
    (slow C a ha0 ha1).mean f=C.mean f := rfl

lemma variance (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f : X → ℝ) :
    (slow C a ha0 ha1).variance f=C.variance f := rfl

/-- Every off-diagonal move and the Dirichlet energy are scaled by the
same holding factor. No irreducibility or nonzero denominator is needed. -/
theorem energy (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f : X → ℝ) :
    (slow C a ha0 ha1).energy f=a*C.energy f := by
  rw [FiniteChain.energy_eq,FiniteChain.energy_eq,←mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change C.π x*(a*C.P x y+if x=y then 1-a else 0)*(f x-f y)^2=
    a*(C.π x*C.P x y*(f x-f y)^2)
  by_cases h : x=y
  · subst y
    simp
  · simp only [h,ite_false,add_zero]
    ring

/-- A holding factor at least one half increases every applicable
variance/energy bound by at most two, including bounds restricted to the
specific observables used by the counting algorithm. -/
theorem variance_bound (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : 1/2 ≤ a) (K : ℝ) (hK : 0 ≤ K) (f : X → ℝ)
    (h : C.variance f ≤ K*C.energy f) :
    (slow C a ha0 ha1).variance f ≤ (2*K)*(slow C a ha0 ha1).energy f := by
  rw [variance,energy]
  have hm := mul_le_mul_of_nonneg_right ha (C.energy_nonneg f)
  have hh := mul_le_mul_of_nonneg_left hm hK
  nlinarith

end

end ContingencyTables.FiniteChainSlowdown

end OAI
