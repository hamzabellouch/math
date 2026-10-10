import OAI.Combinatorics.SquareDifference.SmallRoots

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma exists_large_root (p : ℕ) [Fact p.Prime] (hp : p≠2) (z w : ZMod p)
    (hne : w-z≠0) (hsq : IsSquare (w-z)) : ∃c : ZMod p,c≠0 ∧
      smallRootSquare p c=(w.val:ZMod (smallQuadraticModulus p))-(z.val:ZMod (smallQuadraticModulus p)) := by
  obtain ⟨c,hc⟩ := hsq
  refine ⟨c,(fun h => hne (by simpa only [h,mul_zero] using hc)),?_⟩
  let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast (by simp only [smallQuadraticModulus,hp,ite_false])
  apply e.injective
  simp only [smallRootSquare,hp,ite_false,map_pow,map_natCast,ZMod.natCast_zmod_val,map_sub]
  simpa only [pow_two] using hc.symm

section Roots

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [instFactNatPrimepsi : ∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

noncomputable def selectedRootLabels (s : ZMod (smallModulus ps)) (z : ResidueSpace p) :
    ∀i,ZMod (smallQuadraticModulus (extendedPrime ps p i)) := fun i => match i with
  | Sum.inl j => smallProjection ps j s
  | Sum.inr j => ((z j).val:ZMod (smallQuadraticModulus (p j)))

lemma selectedRootLabels_nat {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J]
    (ps : S → ℕ)
    (p : J → ℕ)
    [∀ (i : S), Fact (Nat.Prime (ps i))]
    [∀ (j : J), Fact (Nat.Prime (p j))] (hp2 : ∀j,p j≠2) (B : Finset J) (s : ZMod (smallModulus ps))
    (z : ResidueSpace p) (n : ℕ) (hn : (n:ZMod (smallModulus ps))=s)
    (hz : ∀j∈B,(n:ZMod (p j))=z j) :
    ∀i∈extendedRoots (S:=S) B,(n:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=selectedRootLabels ps p s z i := by
  intro i hi
  cases i with
  | inl j =>
    change (n:ZMod (smallQuadraticModulus (ps j)))=smallProjection ps j s
    rw [← smallProjection_nat ps j n,hn]
  | inr j =>
    have hj : j∈B := (inr_mem_extendedRoots B j).mp hi
    have hpj := hp2 j
    have he : smallQuadraticModulus (p j)=p j := by simp only [smallQuadraticModulus,hpj,ite_false]
    let e : ZMod (smallQuadraticModulus (p j)) ≃+* ZMod (p j) := RingEquiv.cast he
    change (n:ZMod (smallQuadraticModulus (p j)))=((z j).val:ZMod (smallQuadraticModulus (p j)))
    apply e.injective
    simpa only [map_natCast,ZMod.natCast_zmod_val] using hz j hj

lemma selectedRoot_witnesses (hp2 : ∀j,p j≠2) (B : Finset J)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t) (z w : ResidueSpace p)
    (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
    ∃c : ∀i,ZMod (extendedPrime ps p i),
      (∀i∈extendedRoots (S:=S) B,if extendedPrime ps p i=2 then c i=1 else c i≠0) ∧
      (∀i∈extendedRoots (S:=S) B,smallRootSquare (extendedPrime ps p i) (c i)=
        selectedRootLabels ps p t w i-selectedRootLabels ps p s z i) := by
  classical
  choose cs hcs using (fun i => exists_small_root (ps i) (smallProjection ps i (t-s)) (hst i))
  have hex (j : J) : ∃c : ZMod (p j),c≠0 ∧ (j∈B → smallRootSquare (p j) c=
      ((w j).val:ZMod (smallQuadraticModulus (p j)))-((z j).val:ZMod (smallQuadraticModulus (p j)))) := by
    by_cases hj : j∈B
    · obtain ⟨c,hc,he⟩ := exists_large_root (p j) (hp2 j) (z j) (w j) (hzw j hj).1 (hzw j hj).2
      exact ⟨c,hc,fun _ => he⟩
    · exact ⟨1,one_ne_zero,fun h => False.elim (hj h)⟩
  choose cp hcp using hex
  let c : ∀i,ZMod (extendedPrime ps p i) := fun i => match i with
    | Sum.inl j => cs j
    | Sum.inr j => cp j
  refine ⟨c,?_,?_⟩
  · intro i hi
    cases i with
    | inl j => exact (hcs j).1
    | inr j =>
      change (if p j=2 then cp j=1 else cp j≠0)
      simpa only [hp2,ite_false] using (hcp j).1
  · intro i hi
    cases i with
    | inl j =>
      change smallRootSquare (ps j) (cs j)=smallProjection ps j t-smallProjection ps j s
      simpa only [map_sub] using (hcs j).2
    | inr j => exact (hcp j).2 ((inr_mem_extendedRoots B j).mp hi)

end Roots

end SquareDifference

end

end OAI
