import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
import OAI.NumberTheory.DirichletL.Hecke.Dyadic

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentNaturalPrimitive
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def redundantSet (M C : Ideal O) : Finset (Ideal O) := primeSupport M\primeSupport C

def redundantIdeal (M C : Ideal O) : Ideal O := ∏P∈redundantSet M C,P

lemma redundantSet_prime (M C : Ideal O) : ∀P∈redundantSet M C,Prime P :=
  fun _ h=>support_prime (Finset.mem_sdiff.mp h).1

lemma redundantSet_subset (M C : Ideal O) : redundantSet M C⊆primeSupport M :=
  Finset.sdiff_subset

lemma prime_mem_support_iff (M P : Ideal O) (hM : M≠0) (hP : Prime P) :
    P∈primeSupport M ↔ P∣M := by
  simp only [primeSupport,Multiset.mem_toFinset,Ideal.mem_normalizedFactors_iff hM]
  exact ⟨fun h=>Ideal.dvd_iff_le.mpr h.2,fun h=>⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp h⟩⟩

lemma mem_redundantSet (M C P : Ideal O) (hC : C≠0) :
    P∈redundantSet M C ↔ P∈primeSupport M ∧ ¬P∣C := by
  constructor
  · intro h
    obtain ⟨hp,hc⟩ := Finset.mem_sdiff.mp h
    exact ⟨hp,fun hd=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mpr hd)⟩
  · rintro ⟨hp,hc⟩
    exact Finset.mem_sdiff.mpr ⟨hp,fun h=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mp h)⟩

lemma redundantIdeal_squarefree (M C : Ideal O) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal O) : redundantIdeal M C≠0 :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal O) : primeSupport (redundantIdeal M C)=redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

lemma redundantIdeal_coprime (M C : Ideal O) (hC : C≠0) : IsCoprime (redundantIdeal M C) C := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc=>(Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C*redundantIdeal M C∣M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C.absNorm*(redundantIdeal M C).absNorm≤M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal O) (hM : M≠0) :
    IsCoprime I M ↔ ∀P∈primeSupport M,IsCoprime I P := by
  have hprod (s : Multiset (Ideal O)) : IsCoprime I s.prod ↔ ∀P∈s,IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal O))
    | cons a s ih => simp only [Multiset.prod_cons,IsCoprime.mul_right_iff,Multiset.mem_cons,
        forall_eq_or_imp,ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport,Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀P∈redundantSet M C,IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM,?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC,hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P∈primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP,hPC⟩)

theorem idealCoeff_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (I : Ideal O) :
    idealCoeff χ I=idealCoeff (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)) I := by
  rw [hmask I,idealCoeff_excludePrimes]
  have hm := coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC : IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz : idealCoeff ψ I=0 := by simpa only [hC,ite_false] using idealCoeff_source_mask ψ I
    simp only [hz,ite_self]

theorem polynomial_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (inverse : Bool) (W : ℝ→ℂ) (D σ t : ℝ) :
    HeckeDyadic.polynomial χ inverse W D σ t=
      HeckeDyadic.polynomial (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)) inverse W D σ t := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [idealCoeff_natural_deletion χ ψ hmod hmask I.val]

theorem exists_natural_primitive (χ : Character) :
    ∃ψ : Character,χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (χ.residue≠1 → ψ.residue≠1) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I : Ideal O,idealCoeff χ I=idealCoeff
        (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
          (redundantSet_prime χ.modulus ψ.modulus)) I := by
  obtain ⟨ψ,hmod,hprim,_,hmask⟩ := exists_primitive_character χ
  refine ⟨ψ,hmod,hprim,?_,redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    idealCoeff_natural_deletion χ ψ hmod hmask⟩
  intro hχ hψ
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr hψ)

end SevenEighths.CenteredMomentNaturalPrimitive
end

end OAI
