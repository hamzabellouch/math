import Mathlib
import OAI.Combinatorics.Chromatic.Witness.HistoryMainWitness

namespace OAI

section
namespace ElementaryPositivity.ElementaryRigidity
open scoped BigOperators
open Classical
noncomputable section
variable {n r:ℕ} {R S:Type*} [CommSemiring R] [CommSemiring S]

def eval (n r:ℕ) (R:Type*) [CommSemiring R] :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin r) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>MvPolynomial.esymm (Fin r) R (i.val+1))

def partitionPolynomial (lam:Nat.Partition n) : MvPolynomial (Fin n) R :=
  (lam.parts.attach.map (fun k=>MvPolynomial.X (⟨k.val-1,by
    have hp:=lam.parts_pos k.property
    have hb:=lam.le_of_mem_parts k.property
    omega⟩:Fin n))).prod

lemma eval_partition (lam:Nat.Partition n) (r:ℕ) :
    eval n r R (partitionPolynomial (R:=R) lam)=MvPolynomial.esymmPart (Fin r) R lam := by
  unfold partitionPolynomial MvPolynomial.esymmPart
  rw [map_multiset_prod,Multiset.map_map]
  have he:∀k:{k // k∈lam.parts},
      eval n r R (MvPolynomial.X (⟨k.val-1,by
        have hp:=lam.parts_pos k.property
        have hb:=lam.le_of_mem_parts k.property
        omega⟩:Fin n))=MvPolynomial.esymm (Fin r) R k.val:=by
    intro k
    simp only [eval,MvPolynomial.eval₂Hom_X']
    rw [Nat.sub_add_cancel (lam.parts_pos k.property)]
  simp_rw [Function.comp_def,he]
  have H:=congrArg (fun l:Multiset ℕ=>(l.map (MvPolynomial.esymm (Fin r) R)).prod)
    (Multiset.attach_map_val lam.parts)
  simpa only [Multiset.map_map,Function.comp_def] using H

lemma map_eval (f:R →+* S) (p:MvPolynomial (Fin n) R) :
    MvPolynomial.map f (eval n r R p)=eval n r S (MvPolynomial.map f p) := by
  unfold eval
  rw [MvPolynomial.map_eval₂Hom,MvPolynomial.eval₂Hom_map_hom]
  simp only [MvPolynomial.map_esymm]
  congr 2
  ext x
  simp

lemma eval_injective_ring (R:Type*) [CommRing R] (n:ℕ) : Function.Injective (eval n n R) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective R le_rfl
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply,MvPolynomial.esymmAlgHom_apply]
  exact h

lemma eval_injective_natPolynomial (n:ℕ) : Function.Injective (eval n n (Polynomial ℕ)) := by
  let f:Polynomial ℕ →+* Polynomial ℤ:=Polynomial.mapRingHom (Nat.castRingHom ℤ)
  have hf:Function.Injective f:=Polynomial.map_injective (Nat.castRingHom ℤ) (by intro a b h; change (a:ℤ)=(b:ℤ) at h; exact Int.ofNat_inj.mp h)
  intro p q h
  apply MvPolynomial.map_injective f hf
  apply eval_injective_ring (Polynomial ℤ) n
  rw [←map_eval,←map_eval,h]

lemma eval_C (x:R) : eval n r R (MvPolynomial.C x)=MvPolynomial.C x :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma uniform_of_at_n {A:Type*} [Fintype A] (E:A → ℕ)
    (lam μ:A → Nat.Partition n)
    (h:(∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (μ a))
    (r:ℕ) :
    (∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (μ a) := by
  have he:(∑a,MvPolynomial.C (Polynomial.X^E a)*partitionPolynomial (R:=Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*partitionPolynomial (R:=Polynomial ℕ) (μ a):=by
    apply eval_injective_natPolynomial n
    simpa only [map_sum,map_mul,eval_partition,eval_C] using h
  have H:=congrArg (eval n r (Polynomial ℕ)) he
  simpa only [map_sum,map_mul,eval_partition,eval_C] using H
end
end ElementaryPositivity.ElementaryRigidity

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma test_of_expansion (t:Table n)
    (h:G.chromatic n=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val))) : Test G t := by
  intro a k
  let af:Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun c=>(a c).val)
  have H:=congrArg (fun p:MvPolynomial (Fin n) (Polynomial ℕ)=>(p.coeff af).coeff k.val) h
  rw [chromatic_coefficient,witness_coefficient] at H
  exact H

lemma expansion_of_test (t:Table n) (ht:Test G t) :
    G.chromatic n=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val)) := by
  apply MvPolynomial.ext
  intro a
  by_cases ha:a.degree=n
  · apply Polynomial.ext
    intro k
    rw [chromatic_coefficient,witness_coefficient]
    by_cases hk:k≤G.edgeCount
    · let af:Fin n → Fin (n+1):=fun c=>⟨a c,by have H:=Finsupp.le_degree c a; omega⟩
      exact ht af ⟨k,Nat.lt_succ_of_le hk⟩
    · rw [colorCount_zero_high G a k (by omega),witnessCount_zero_high G t a k (by omega)]
  · rw [chromatic_degree_zero G a ha,MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [MvPolynomial.coeff_C_mul,row_degree_zero _ _ ha,mul_zero]

lemma uniform_expansion_of_test (W:G.PermutationWitness) (t:Table n) (ht:Test G t) (r:ℕ) :
    G.chromatic r=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (rowPartition (t σ.val)) := by
  trans ∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
    MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
      MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (W.theta σ)
  · exact W.expansion r
  · apply ElementaryRigidity.uniform_of_at_n
      (fun σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ}=>G.graphInversions σ.val)
      W.theta (fun σ=>rowPartition (t σ.val))
    trans G.chromatic n
    · exact (W.expansion n).symm
    · exact expansion_of_test G t ht

lemma exists_test (W:G.PermutationWitness) : ∃t:Table n,Test G t := by
  let p0:Nat.Partition n:=Nat.Partition.ofSums n {n} (by simp)
  let p:(Fin n → Fin n) → Nat.Partition n:=fun w=>
    if hw:WordOK G w then W.theta ⟨Equiv.ofBijective w hw.1,hw.2⟩ else p0
  let t:Table n:=fun w=>Classical.choose (rowPartition_surjective n (p w))
  have he:∀σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},rowPartition (t σ.val)=W.theta σ:=by
    intro σ
    have H:rowPartition (t σ.val)=p σ.val:=Classical.choose_spec (rowPartition_surjective n (p σ.val))
    rw [H]
    have hp:WordOK G σ.val:=⟨σ.val.bijective,σ.property⟩
    dsimp only [p]
    rw [dite_eq_left hp]
    congr 1
    apply Subtype.ext
    exact Equiv.ext (fun _=>rfl)
  refine ⟨t,test_of_expansion G t ?_⟩
  simp_rw [he]
  exact W.expansion n
end
end ElementaryPositivity.FiniteSearch

end

end OAI
