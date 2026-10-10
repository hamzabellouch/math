import OAI.Combinatorics.SquareDifference.SmallGood

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma multilinear_exceptional_bound {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
    (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j) (F : V → (∀j,X j) → ℝ) :
    |multilinearIntegral (tensorLaw L) F|≤|multilinearIntegral (tensorLaw G) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (mixedTensorLaw L E B) F| :=
  tensorLaw_exceptional_bound L E hL G eta heta hdec (fun z => ∏v,F v (z v))

lemma tuple_multilinear_exceptional_bound {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L E : ∀j,((TupleVertex → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((TupleVertex → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j) (F : TupleVertex → ResidueSpace p → ℝ) :
    |multilinearIntegral (tensorLaw L) F|≤|multilinearIntegral (tensorLaw G) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (mixedTensorLaw L E B) F| :=
  multilinear_exceptional_bound L E hL G eta heta hdec F

section Average

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actualLift_expect {I : Type*} [Fintype I] (N Q : ℕ) (f : I → ℕ → ℝ) (x : ResidueSpace p) :
    actualTruncatedLift p N Q (fun n => 𝔼 i,f i n) x=(𝔼 i,actualTruncatedLift p N Q (f i) x) := by
  change (∑U∈liftSupportFamily p Q,(N:ℝ)⁻¹*∑n∈range N,(𝔼 i,f i n)*LiftTheory.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))))=_
  simp_rw [expect_mul]
  simp_rw [←expect_sum_comm,mul_expect]
  rw [←expect_sum_comm]
  rfl

lemma setFunctional_small_average (N Q M : ℕ) [NeZero M] (A : Finset ℕ) :
    setFunctional p N Q A=𝔼 s : TupleVertex → ZMod M,
      multilinearIntegral (productTupleLaw p) (fun v => actualTruncatedLift p N Q (smallResidueInput M A (s v))) := by
  have he (x : ResidueSpace p) : actualTruncatedLift p N Q (natIndicator A) x=
      𝔼 s : ZMod M,actualTruncatedLift p N Q (smallResidueInput M A s) x := by
    rw [←actualLift_expect]
    simp only [smallResidueInput_average]
  change multilinearIntegral (productTupleLaw p) (fun _ => actualTruncatedLift p N Q (natIndicator A))=_
  rw [show actualTruncatedLift p N Q (natIndicator A)=(fun x => 𝔼 s : ZMod M,actualTruncatedLift p N Q (smallResidueInput M A s) x) from funext he]
  simpa only [one_mul,one_pow] using multilinearIntegral_scale_expect
    (I:=ZMod M) (productTupleLaw p) (fun (_v : TupleVertex) (s : ZMod M) (x : ResidueSpace p) => actualTruncatedLift p N Q (smallResidueInput M A s) x) 1

lemma actualMixedLaw_empty : actualMixedLaw p ∅=productTupleLaw p := by
  rw [actualMixedLaw,mixedTensorLaw_empty]
  rfl

lemma actual_exceptional_bound (hp : ∀j,tupleMassThreshold≤(p j:ℝ))
    (heta : ∀j,tupleEta (p j)≤1) (F : TupleVertex → ResidueSpace p → ℝ) :
    |multilinearIntegral (productTupleLaw p) F|≤
      |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (actualMixedLaw p B) F| := by
  exact tuple_multilinear_exceptional_bound p (fun j => tupleLaw (p:=p j)) (fun j => tupleExceptionalLaw (p:=p j))
    (fun j => tupleLaw_probability (p:=p j) (hp j)) (fun j => tupleGoodLaw (p:=p j)) (fun j => tupleEta (p j))
    (fun j => ⟨tupleEta_nonneg (p j),heta j⟩)
    (fun j => sub_eq_iff_eq_add.mpr (tupleLaw_decomposition (p:=p j) (hp j))) F

end Average

lemma event_average_bound {I : Type*} [Fintype I] [Nonempty I] (P : I → Prop) [DecidablePred P]
    (F : I → ℝ) (G B : ℝ) (hg : ∀i,P i → |F i|≤G) (hb : ∀i,¬P i → |F i|≤B) :
    |𝔼 i,F i|≤(𝔼 i,if P i then (1:ℝ) else 0)*G+(1-(𝔼 i,if P i then (1:ℝ) else 0))*B := by
  apply (abs_expect_le _ _).trans
  calc
    _ ≤ 𝔼 i : I,((if P i then (1:ℝ) else 0)*G+(1-(if P i then (1:ℝ) else 0))*B) := by
      apply expect_le_expect
      intro i _
      split_ifs with hi
      · simpa only [one_mul,sub_self,zero_mul,add_zero] using hg i hi
      · simpa only [zero_mul,sub_zero,one_mul,zero_add] using hb i hi
    _ = _ := by rw [expect_add_distrib,←expect_mul,←expect_mul,expect_sub_distrib,Fintype.expect_const]

end SquareDifference

end

end OAI
