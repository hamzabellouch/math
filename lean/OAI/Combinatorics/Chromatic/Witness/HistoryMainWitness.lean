import Mathlib
import OAI.Combinatorics.Chromatic.Witness.ElementaryProductDegree

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph

noncomputable def historyWitness {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n) : G.PermutationWitness:=
  G.ofAdmissibleWitness (TriangularDynamics.admissiblePartition G)
    (TriangularDynamics.admissible_polynomial_expansion G)
end ElementaryPositivity.NaturalUnitIntervalGraph

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators

abbrev Row (n:ℕ):={v:Fin n → Fin (n+1) // ∑i,(v i).val=n}

def rowPartition {n:ℕ} (v:Row n):Nat.Partition n:=
  Nat.Partition.ofSums n (Finset.univ.val.map (fun i=>(v.val i).val)) v.property

lemma rowPartition_surjective (n:ℕ) : Function.Surjective (@rowPartition n) := by
  intro p
  obtain ⟨l,hl⟩:=Quotient.exists_rep p.parts
  have hl':(l:Multiset ℕ)=p.parts:=hl
  have hsum:l.sum=n:=by simpa only [←hl',Multiset.sum_coe] using p.parts_sum
  have hpos:∀i∈l,0 < i:=by intro i hi; exact p.parts_pos (by simpa only [←hl',Multiset.mem_coe] using hi)
  have hlen:l.length≤n:=hsum ▸ List.length_le_sum_of_one_le l hpos
  let L:=l++List.replicate (n-l.length) 0
  have hL:L.length=n:=by simp [L]; omega
  have hbL:∀x∈L,x≤n:=by
    intro x hx
    simp only [L,List.mem_append,List.mem_replicate] at hx
    rcases hx with hx|⟨_,hx⟩
    · exact p.le_of_mem_parts (by simpa only [←hl',Multiset.mem_coe] using hx)
    · omega
  let v:Fin n → Fin (n+1):=fun i=>⟨L[i.val]'(by omega),
    Nat.lt_succ_of_le (hbL _ (List.getElem_mem (by omega)))⟩
  have hv:List.ofFn (fun i:Fin n=>(v i).val)=L:=by
    apply List.ext_getElem
    · simp [hL]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hm:(Finset.univ.val.map (fun i:Fin n=>(v i).val):Multiset ℕ)=L:=by
    rw [Finset.val_univ_fin]
    change (List.map (fun i:Fin n=>(v i).val) (List.finRange n):Multiset ℕ)=_
    rw [←List.ofFn_eq_map,hv]
  have hvsum:(∑i:Fin n,(v i).val)=n:=by
    change (Finset.univ.val.map (fun i:Fin n=>(v i).val)).sum=n
    rw [hm,Multiset.sum_coe]
    simp [L,hsum]
  refine ⟨⟨v,hvsum⟩,?_⟩
  apply Nat.Partition.ext
  change (Finset.univ.val.map (fun i:Fin n=>(v i).val)).filter (·≠0)=p.parts
  rw [hm,←hl']
  have hf:(l:Multiset ℕ).filter (·≠0)=(l:Multiset ℕ):=
    Multiset.filter_eq_self.mpr (by intro i hi; exact (hpos i hi).ne')
  simpa [L] using hf

end ElementaryPositivity.FiniteSearch

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

abbrev Table (n:ℕ):=(Fin n → Fin n) → Row n

def WordOK (w:Fin n → Fin n):Prop:=Function.Bijective w ∧
  ∀i j:Fin n,i.val+1=j.val → w j<w i → G.Edge (w i) (w j)
instance (w:Fin n → Fin n):Decidable (WordOK G w):=
  inferInstanceAs (Decidable (Function.Bijective w ∧ ∀i j:Fin n,
    i.val+1=j.val → w j<w i → G.Edge (w i) (w j)))

def wordEnergy (w:Fin n → Fin n):ℕ:=
  (Finset.univ.filter fun ij:Fin n × Fin n=>
    ij.1 < ij.2 ∧ w ij.2 < w ij.1 ∧ G.Edge (w ij.1) (w ij.2)).card

def colorCount (a:Fin n → ℕ) (k:ℕ):ℕ:=∑κ:Fin n → Fin n,
  if G.Proper κ ∧ (∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c) ∧ G.coloringAscents κ=k then 1 else 0

def matrixCount (v:Row n) (a:Fin n → ℕ):ℕ:=∑s:Fin n → Finset (Fin n),
  if (∀i,(s i).card=(v.val i).val) ∧
    (∀c,(Finset.univ.filter (fun i=>c∈s i)).card=a c) then 1 else 0

def witnessCount (t:Table n) (a:Fin n → ℕ) (k:ℕ):ℕ:=∑w:Fin n → Fin n,
  if WordOK G w ∧ wordEnergy G w=k then matrixCount (t w) a else 0

def Test (t:Table n):Prop:=∀a:Fin n → Fin (n+1),∀k:Fin (G.edgeCount+1),
  colorCount G (fun c=>(a c).val) k.val=witnessCount G t (fun c=>(a c).val) k.val
instance (t:Table n):Decidable (Test G t):=inferInstanceAs (Decidable (∀a:Fin n → Fin (n+1),
  ∀k:Fin (G.edgeCount+1),colorCount G (fun c=>(a c).val) k.val=witnessCount G t (fun c=>(a c).val) k.val))

end ElementaryPositivity.FiniteSearch

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Packets
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def rowProfile (v:Row n):Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun i=>(v.val i).val)
lemma rowProfile_degree (v:Row n):(rowProfile v).degree=n:=by
  rw [Finsupp.degree_eq_sum]
  exact v.property
lemma rowPartition_eq_profile (v:Row n):rowPartition v=profilePartition (rowProfile v) (rowProfile_degree v):=rfl

lemma matrix_coefficient {R:Type*} [CommSemiring R] (v:Row n) (a:Fin n →₀ ℕ) :
    (MvPolynomial.esymmPart (Fin n) R (rowPartition v)).coeff a=(matrixCount v a:R) := by
  rw [rowPartition_eq_profile,esymmPart_profile,ElementaryMatrix.elementary_product_coeff]
  simp only [matrixCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro s hs
  have hr:ElementaryMatrix.rowCount s=rowProfile v ↔ ∀i,(s i).card=(v.val i).val:=
    ElementaryMatrix.rowCount_eq s _
  have hc:ElementaryMatrix.colCount s=a ↔ ∀c,(Finset.univ.filter (fun i=>c∈s i)).card=a c:=by
    rw [Finsupp.ext_iff]
    simp only [ElementaryMatrix.colCount_apply,ElementaryMatrix.transpose]
  simp only [hr,hc]

lemma chromatic_coefficient (a:Fin n →₀ ℕ) (k:ℕ) :
    ((G.chromatic n).coeff a).coeff k=colorCount G a k := by
  have he:∀κ:Fin n → Fin n,wordCount κ=a ↔ ∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c:=by
    intro κ
    rw [Finsupp.ext_iff]
    simp only [wordCount_apply]
  unfold NaturalUnitIntervalGraph.chromatic colorCount
  rw [MvPolynomial.coeff_sum,Polynomial.finsetSum_coeff,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro κ hκ
  by_cases hp:G.Proper κ
  · simp only [hp,ite_true,true_and,coloring_monomial,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_monomial]
    by_cases ha:wordCount κ=a
    · simp only [ha,ite_true,mul_one,Polynomial.coeff_X_pow,(he κ).mp ha]
      simp [eq_comm]
    · simp only [ha,ite_false,mul_zero,Polynomial.coeff_zero,(he κ).not.mp ha,false_and]
  · simp [hp]

lemma chromatic_degree_zero (a:Fin n →₀ ℕ) (ha:a.degree≠n):
    (G.chromatic n).coeff a=0 := by
  ext k
  rw [chromatic_coefficient,Polynomial.coeff_zero,colorCount]
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨_,hc,_⟩
  have hca:wordCount κ=a:=by ext c; rw [wordCount_apply]; exact hc c
  exact ha (hca ▸ wordCount_degree κ)

def wordEquiv : {σ:Equiv.Perm (Fin n) // G.Nondescent σ} ≃ {w:Fin n → Fin n // WordOK G w} where
  toFun σ:=⟨σ.val,σ.val.bijective,σ.property⟩
  invFun w:=⟨Equiv.ofBijective w.val w.property.1,w.property.2⟩
  left_inv σ:=by apply Subtype.ext; exact Equiv.ext (fun _=>rfl)
  right_inv _:=rfl

lemma witness_coefficient (t:Table n) (a:Fin n →₀ ℕ) (k:ℕ) :
    ((∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
      MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val))).coeff a).coeff k=
      witnessCount G t a k := by
  rw [←Equiv.sum_comp (wordEquiv G).symm]
  rw [MvPolynomial.coeff_sum,Polynomial.finsetSum_coeff]
  change (∑w:{w:Fin n → Fin n // WordOK G w},
    ((MvPolynomial.C (Polynomial.X^wordEnergy G w.val)*
      MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t w.val))).coeff a).coeff k)=_
  simp only [MvPolynomial.coeff_C_mul,matrix_coefficient,Polynomial.coeff_mul_natCast,Polynomial.coeff_X_pow,Nat.cast_id]
  rw [sum_subtype_ite (WordOK G) (fun w => (if k = wordEnergy G w then 1 else 0) * (matrixCount (t w) a : ℕ))]
  unfold witnessCount
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hp:WordOK G w
  · by_cases hk:wordEnergy G w=k
    · simp [hp,hk]
    · have hk':k≠wordEnergy G w:=Ne.symm hk
      simp [hp,hk,hk']
  · simp [hp]

lemma row_degree_zero (v:Row n) (a:Fin n →₀ ℕ) (ha:a.degree≠n) :
    (MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition v)).coeff a=0 := by
  rw [rowPartition_eq_profile,esymmPart_profile]
  exact ElementaryMatrix.elementary_product_coeff_zero _ _ (by simpa only [rowProfile_degree] using ha)

lemma colorCount_zero_high (a:Fin n → ℕ) (k:ℕ) (hk:G.edgeCount<k):colorCount G a k=0 := by
  unfold colorCount
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨hp,_,he⟩
  have h:=G.coloringInversions_add_ascents κ hp
  omega
lemma witnessCount_zero_high (t:Table n) (a:Fin n → ℕ) (k:ℕ) (hk:G.edgeCount<k):witnessCount G t a k=0 := by
  unfold witnessCount
  apply Finset.sum_eq_zero
  intro w hw
  rw [ite_eq_right]
  rintro ⟨hp,he⟩
  have h:=G.graphInversions_le_edges (Equiv.ofBijective w hp.1)
  change wordEnergy G w≤G.edgeCount at h
  omega
end
end ElementaryPositivity.FiniteSearch

end

end OAI
