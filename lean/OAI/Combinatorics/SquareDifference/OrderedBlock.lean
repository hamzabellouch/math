import OAI.Combinatorics.SquareDifference.BlockParameters

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def orderedLowError (d M K H : ℕ) (R : ℝ) : ℝ :=
  (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*((K:ℝ)^2*M*kernelAbsoluteConstant+R^2)

lemma orderedLowError_nonneg (d M K H : ℕ) (R : ℝ) : 0≤orderedLowError d M K H R := by
  unfold orderedLowError
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))

lemma ordered_low_cost (d m M N L K H : ℕ) (hm : m≤d) (hM : 1≤M) (hK : 1≤K)
    (hNL : (N:ℝ)/L≤K) (R : ℝ) :
    ((M:ℝ)*(K:ℝ)^2)^m*((K:ℝ)^d*(H:ℝ)^(-(1:ℝ)/3)*
      (((N:ℝ)/L)^2*M*kernelAbsoluteConstant+R^2))≤orderedLowError d M K H R := by
  have hb : 1≤(M:ℝ)*(K:ℝ)^2 := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hM) (one_le_pow₀ (by exact_mod_cast hK))
  have hn : 0≤(N:ℝ)/L := by positivity
  have hs : ((N:ℝ)/L)^2*M*kernelAbsoluteConstant+R^2≤(K:ℝ)^2*M*kernelAbsoluteConstant+R^2 := by
    exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn hNL 2)
      (Nat.cast_nonneg M)) kernelAbsoluteConstant_nonneg) le_rfl
  calc
    _ ≤ ((M:ℝ)*(K:ℝ)^2)^d*((K:ℝ)^d*(H:ℝ)^(-(1:ℝ)/3)*
        ((K:ℝ)^2*M*kernelAbsoluteConstant+R^2)) := by
      apply mul_le_mul (pow_le_pow_right₀ hb hm) _ (by
        exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))) (by positivity)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by unfold orderedLowError; rw [mul_pow,←pow_mul,show 3*d=2*d+d by omega,pow_add]; ring

section Ordered

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma ordered_interval_full (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H K : ℕ) (hN : 1≤N) (hH : 1≤H) (hK : 1≤K)
    (hHQ : H*K^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(K^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (hNL : (N:ℝ)/L≤K) (R : ℝ) (hR : 0≤R)
    (hm : ∀v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,intervalPiece p (a v) L (smallResidueInput (smallModulus ps) A (s v)) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)))|≤
      (Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
        orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R := by
  have ht := interval_truncation_error p hmass a L Q K (by omega) {cycleVertex k,cycleVertex (k+1)}
    (fun v => smallResidueInput (smallModulus ps) A (s v)) R hR hm
  have hl := ordered_low_bound ps p hinj hp (fun j => (le_max_left _ _).trans (hmass j)) a L N Q H K
    hN hH hK hHQ hD hHn hlarge hcover A hA hfree s k hab hst R
    (fun v => interval_two_moment p a L Q _ R hm v _ Subset.rfl)
  have hc := ordered_low_cost (Fintype.card TupleVertex) (Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1)))) (smallModulus ps) N L K H
    (by have := otherVertices_card (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k); omega)
    (show 1≤ smallModulus ps from prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (ps i).Prime))) hK hNL R
  have htri (x y : ℝ) : |x|≤|x-y|+|y| := by simpa only [sub_add_cancel] using abs_add_le (x-y) y
  exact (htri _ _).trans (add_le_add ht (hl.trans hc))

lemma blockLift_expect (N K L Q : ℕ) (hN : 0<N) (hK : 0<K) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    actualTruncatedLift p N Q f x=((K:ℝ)*L/N)*(𝔼 i : Fin K,intervalLift p (L*i.val) L Q f x) := by
  rw [blockLift_decomposition p N K L Q hN hL hcover f hf,expect_eq_sum_div_card,card_univ,Fintype.card_fin]
  rw [←Fin.sum_univ_eq_sum_range]
  have hk : (K:ℝ)≠0 := Nat.cast_ne_zero.mpr hK.ne'
  field_simp

end Ordered

end SquareDifference

end

end OAI
