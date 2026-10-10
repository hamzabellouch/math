import OAI.Combinatorics.SquareDifference.OrderedLow

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma pow_le_one_add_pow {x : ℝ} (hx : 0≤x) {m n : ℕ} (hmn : m≤n) :
    x^m≤1+x^n := by
  by_cases h : x≤1
  · exact (pow_le_one₀ hx h).trans (le_add_of_nonneg_right (pow_nonneg hx _))
  · exact (pow_le_pow_right₀ (le_of_not_ge h) hmn).trans (le_add_of_nonneg_left zero_le_one)

lemma uniform_multilinear_crude {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F : V → X → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F|≤2*R^(2*Fintype.card V) := by
  apply positiveLaw_product_bound Llaw hpos (fun v z => F v (z v)) _
  intro v
  rw [hmar v (fun x => |F v x|^(Fintype.card V))]
  have hd : 2≤Fintype.card V := Fintype.one_lt_card
  have hn : Fintype.card V≤2*(Fintype.card V-1) := by omega
  have hpow : R^(2*(Fintype.card V-1))≤R^(2*Fintype.card V) :=
    pow_le_pow_right₀ hR (by omega)
  calc
    _ ≤ 𝔼 x : X,(1+|F v x|^(2*(Fintype.card V-1))) :=
      expect_le_expect (fun x _ => pow_le_one_add_pow (abs_nonneg _) hn)
    _ = 1+(𝔼 x : X,F v x^(2*(Fintype.card V-1))) := by
      rw [expect_add_distrib,Fintype.expect_const]
      simp only [(even_two_mul _).pow_abs]
    _ ≤ 1+R^(2*(Fintype.card V-1)) := add_le_add le_rfl (hm v (Fintype.card V-1) (by omega))
    _ ≤ _ := by have hp : 1≤R^(2*Fintype.card V) := one_le_pow₀ hR; linarith

lemma interval_multilinear_crude {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => intervalLift p (a v) L Q (f v))|≤2*R^(2*Fintype.card TupleVertex) := by
  exact uniform_multilinear_crude _ (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg))
    (tensorGood_uniform_marginal p hp) _ R hR (interval_full_moment p a L Q f R hm)

end SquareDifference

end

end OAI
