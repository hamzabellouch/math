import OAI.NumberTheory.DirichletL.Moments.DivisorAllocation

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [ite_eq_right h])

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩

theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm

theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
