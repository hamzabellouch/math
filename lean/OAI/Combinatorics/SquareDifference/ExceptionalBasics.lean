import OAI.Combinatorics.SquareDifference.IntervalContraction

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma tupleExceptionalLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p:ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleExceptionalLaw (fun z => f (z v))=tupleEta p*(𝔼 x,f x) := by
  have h := congrArg (fun L : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ => L (fun z => f (z v))) (tupleLaw_decomposition hp)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,tupleLaw_marginal hp,tupleGoodLaw_marginal hp] at h
  linarith

lemma tensorLaw_weighted_marginal {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (v : V) (c : J → ℝ)
    (hm : ∀j (g : X j → ℝ),L j (fun z => g (z v))=c j*(𝔼 x,g x))
    (f : (∀j,X j) → ℝ) : tensorLaw L (fun z => f (z v))=(∏j,c j)*(𝔼 x,f x) := by
  have hd (a : ∀j,X j) : tensorLaw L (fun z => if z v=a then 1 else 0)=
      (∏j,c j)*(Fintype.card (∀j,X j) : ℝ)⁻¹ := by
    have he (z : V → ∀j,X j) : (if z v=a then (1:ℝ) else 0)=
        ∏j,if z v j=a j then 1 else 0 := by
      rw [prod_indicator_forall]
      congr 1
      exact propext (funext_iff)
    simp_rw [he]
    rw [tensorLaw_fubini L (fun j z => if z v=a j then 1 else 0)]
    have hh (j : J) : L j (fun z => if z v=a j then (1:ℝ) else 0)=
        c j*(𝔼 x : X j, if x=a j then (1:ℝ) else 0) := hm j (fun x => if x=a j then 1 else 0)
    simp_rw [hh]
    simp only [prod_mul_distrib,expect_eq_sum_div_card,card_univ,sum_ite_eq',mem_univ,ite_true,
      one_div,←prod_inv_distrib,Fintype.card_pi,Nat.cast_prod]
  have hf : (fun z : V → ∀j,X j => f (z v))=
      ∑a : ∀j,X j,f a • (fun z => if z v=a then (1:ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp
  rw [hf,map_sum]
  simp only [map_smul,smul_eq_mul,hd,←mul_assoc,←sum_mul,expect_eq_sum_div_card,card_univ,div_eq_mul_inv]
  ring

lemma weighted_uniform_multilinear_crude {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (c : ℝ) (hc : 0≤c)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=c*(𝔼 x,g x))
    (F : V → X → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F|≤c*(2*R^(2*Fintype.card V)) := by
  apply positiveLaw_product_bound Llaw hpos (fun v z => F v (z v)) _
  intro v
  rw [hmar v (fun x => |F v x|^(Fintype.card V))]
  apply mul_le_mul_of_nonneg_left _ hc
  have hd : 2≤Fintype.card V := Fintype.one_lt_card
  have hn : Fintype.card V≤2*(Fintype.card V-1) := by omega
  have hpow : R^(2*(Fintype.card V-1))≤R^(2*Fintype.card V) := pow_le_pow_right₀ hR (by omega)
  calc
    _ ≤ 𝔼 x : X,(1+|F v x|^(2*(Fintype.card V-1))) :=
      expect_le_expect (fun x _ => pow_le_one_add_pow (abs_nonneg _) hn)
    _ = 1+(𝔼 x : X,F v x^(2*(Fintype.card V-1))) := by
      rw [expect_add_distrib,Fintype.expect_const]
      simp only [(even_two_mul _).pow_abs]
    _ ≤ 1+R^(2*(Fintype.card V-1)) := add_le_add le_rfl (hm v (Fintype.card V-1) (by omega))
    _ ≤ _ := by have hp : 1≤R^(2*Fintype.card V) := one_le_pow₀ hR; linarith

section Mixed

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

noncomputable def exceptionalProduct (B : Finset J) : ℝ := ∏j∈B,tupleEta (p j)

noncomputable def actualMixedLaw (B : Finset J) : ((TupleVertex → ∀j,ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ :=
  mixedTensorLaw (fun j => tupleLaw (p:=p j)) (fun j => tupleExceptionalLaw (p:=p j)) B

lemma exceptionalProduct_nonneg {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) : 0≤exceptionalProduct p B := prod_nonneg (fun _ _ => tupleEta_nonneg _)

lemma actualMixedLaw_nonneg (B : Finset J) (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) (hF : ∀z,0≤F z) :
    0≤actualMixedLaw p B F := mixedTensorLaw_nonneg _ _ (fun _ => tupleLaw_nonneg) (fun _ => tupleExceptionalLaw_nonneg) B F hF

lemma actualMixedLaw_marginal (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (v : TupleVertex) (g : (∀j,ZMod (p j)) → ℝ) :
    actualMixedLaw p B (fun z => g (z v))=exceptionalProduct p B*(𝔼 x,g x) := by
  have h := tensorLaw_weighted_marginal (fun j => if j∈B then tupleExceptionalLaw (p:=p j) else tupleLaw (p:=p j))
    v (fun j => if j∈B then tupleEta (p j) else 1) (fun j f => by
      by_cases hj : j∈B
      · simp only [hj,ite_true]; exact tupleExceptionalLaw_marginal (hp j) v f
      · simp only [hj,ite_false,one_mul]; exact tupleLaw_marginal (hp j) v f) g
  simpa only [prod_ite_mem,univ_inter,actualMixedLaw,mixedTensorLaw,exceptionalProduct] using h

lemma actualMixedLaw_mass (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J) :
    actualMixedLaw p B (fun _ : TupleVertex → ∀j,ZMod (p j) => (1:ℝ))=exceptionalProduct p B := by
  have h := actualMixedLaw_marginal p hp B (Classical.arbitrary TupleVertex) (fun _ => (1:ℝ))
  simpa only [Fintype.expect_const,mul_one] using h

lemma actualMixedLaw_crude (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (F : TupleVertex → (∀j,ZMod (p j)) → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card TupleVertex → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral (actualMixedLaw p B) F|≤exceptionalProduct p B*(2*R^(2*Fintype.card TupleVertex)) :=
  weighted_uniform_multilinear_crude _ (actualMixedLaw_nonneg p B) _ (exceptionalProduct_nonneg p B)
    (actualMixedLaw_marginal p hp B) F R hR hm

end Mixed

end SquareDifference

end

end OAI
