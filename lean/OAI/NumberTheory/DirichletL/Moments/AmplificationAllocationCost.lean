import OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSupport IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentCommonSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem allocation_slot_one (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (i : ι) : B.val (Sum.inl i)=1 := by
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hi := Fintype.mem_piFinset.mp hv (Sum.inl i)
  have hd := hslot i (v (Sum.inl i)) hi
  have he := congrFun hvB (Sum.inl i)
  have hc : IsCoprime (P^k) (v (Sum.inl i)) := hd.2.pow_left
  have hh := supportExtract_of_disjoint (v (Sum.inl i)) (primeSupport (P^k))
    ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff (pow_ne_zero k hP) hd.1).mpr hc).symm
  exact he.symm.trans hh

 theorem allocation_plain_product (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : B.val (Sum.inr 0)*B.val (Sum.inr 1)=P^k := by
  have he := (Finset.mem_filter.mp B.property).2
  rw [Fintype.prod_sum_type,show (∏ i : ι,B.val (Sum.inl i))=1 by
    simp only [allocation_slot_one S P hP k hslot B,Finset.prod_const_one],one_mul,
    Fin.prod_univ_two] at he
  exact he

 theorem allocation_plain_injective (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    Function.Injective (fun B : actualAllocations S (P^k) => B.val (Sum.inr 0)) := by
  intro B D he
  have hb := allocation_plain_product S P hP k hslot B
  have hd := allocation_plain_product S P hP k hslot D
  have hb0 := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1 (Sum.inr 0)
  have he1 : B.val (Sum.inr 1)=D.val (Sum.inr 1) := by
    apply mul_left_cancel₀ hb0
    exact (hb.trans hd.symm).trans (congrArg (fun x => x*D.val (Sum.inr 1)) he.symm)
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rw [allocation_slot_one S P hP k hslot B,allocation_slot_one S P hP k hslot D]
  | inr i => fin_cases i <;> assumption

 theorem idealDivisors_prime_power_card (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (idealDivisors (P^k)).card≤k+1 := by
  have hs : idealDivisors (P^k)⊆(Finset.range (k+1)).image (fun j => P^j) := by
    intro I hI
    obtain ⟨j,hj,he⟩ := (dvd_prime_pow hP k).mp ((mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mp hI)
    have heq : I=P^j := dvd_antisymm he.dvd he.symm.dvd
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),heq.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range (k+1)))

theorem actual_amplification_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤k+1 := by
  let f : actualAllocations S (P^k) → idealDivisors (P^k) := fun B =>
    ⟨B.val (Sum.inr 0),(mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mpr
      ⟨B.val (Sum.inr 1),(allocation_plain_product S P hP.ne_zero k hslot B).symm⟩⟩
  have hf : Function.Injective f := by
    intro B D he
    exact allocation_plain_injective S P hP.ne_zero k hslot (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  exact hh.trans (idealDivisors_prime_power_card P hP k)

 theorem actual_error_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤8 := by
  have hh := actual_amplification_allocations_card S P hP k hslot
  rcases hk with rfl|rfl|rfl <;> omega

end SevenEighths.CenteredMomentAmplificationAllocationCost

end

end OAI
