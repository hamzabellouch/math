import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceReindex
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem tuple_supported (L:ι→Finset (Ideal O))(hs:∀i,∀P∈L i,Supported P)(q:Tuple L) :
    Supported (∏i,(q i).val) := by
  have hh (T:Finset ι):Supported (∏i∈T,(q i).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi]
      exact (supported_mul_iff _ _).mpr ⟨hs i _ (q i).property,ih⟩
  exact hh Finset.univ

theorem tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Admissible (∏i,(q i).val) :=
  ⟨(tuple_supported L hs q).1,tuple_product_squarefree _ (fun i=>hp i _ (q i).property)
    (tuple_injective L hdis q),(tuple_supported L hs q).2⟩

def remainingFromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) : Remaining L J :=
  fun i=>⟨t i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp ht i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩

theorem remainingIdeal_fromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    remainingIdeal L J (remainingFromPi L J t ht)=survivingProduct (Finset.univ\J) t := by
  unfold remainingIdeal
  rw [remaining_product_attach]
  rfl

theorem remaining_tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(t:∀i∈Finset.univ\J,Ideal O)
    (ht:t∈(Finset.univ\J).pi L) :
    Admissible (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_admissible L hp hs hdis _

theorem remaining_tuple_coprime (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    Pairwise (Function.onFun IsCoprime (fun i:↥(Finset.univ\J)=>t i.val i.property)) := by
  intro i j hij
  have hiP:=hp i.val _ (Finset.mem_pi.mp ht i.val i.property)
  have hjP:=hp j.val _ (Finset.mem_pi.mp ht j.val j.property)
  let:(t i.val i.property).IsMaximal:=(Ideal.isPrime_of_prime hiP).isMaximal hiP.ne_zero
  let:(t j.val j.property).IsMaximal:=(Ideal.isPrime_of_prime hjP).isMaximal hjP.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  dsimp only at he
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val)
    (fun hh=>hij (Subtype.ext hh))) (Finset.mem_pi.mp ht i.val i.property)
      (by rw [he];exact Finset.mem_pi.mp ht j.val j.property)

omit [DecidableEq ι] in
theorem tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(q:Tuple L) : outside E (∏i,(q i).val) := by
  intro P hP hd
  obtain ⟨i,hi,hdi⟩:=((hE P hP).dvd_finsetProd_iff (fun i=>(q i).val)).mp hd
  exact hout i _ (q i).property P hP hdi

theorem remaining_tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(J:Finset ι)(x:Assigned L J)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    outside E (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_outside L E hE hout _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
