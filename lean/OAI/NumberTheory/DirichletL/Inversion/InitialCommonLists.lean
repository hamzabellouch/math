import OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples
import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def poolList (F:Finset (Ideal Eis))(L:Finset (Ideal Eis)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=>i.val∈L)

theorem outside_pool_not_dvd (F:Finset (Ideal Eis))(A:Finset (primePool F))
    {P:Ideal Eis}(hP:Prime P)(hn:P∉primePool F) : ¬P∣∏i∈A,i.val := by
  intro hd
  obtain ⟨i,hi,hd⟩ := hP.dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
  have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have he := (prime_dvd_prime_iff_eq hP hip).mp hd
  exact hn (he ▸ i.property)

theorem dividing_list_image (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
    ((poolList F L).filter (fun i=>i∈A)).image Subtype.val=
      L.filter (fun P=>P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

theorem original_ideal_slot (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(a:Ideal Eis→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=>Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal Eis))(I:Finset σ)
    (L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (hL i hi) (a i) A

end SevenEighths.InverseInitialCommonLists

end

end OAI
