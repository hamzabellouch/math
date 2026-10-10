import OAI.NumberTheory.DirichletL.PrimeRows.Character
import OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal
import OAI.NumberTheory.DirichletL.Hecke.UnitRows
import OAI.NumberTheory.DirichletL.UnitSexticWitness

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
open CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma rawRow_elementCoeff (u : FreeRow) (n : O) :
    elementCoeff (rawRow u) n = rowTwist (HeckeRowClosure.elementHom
      (fixedSourcePrincipal ∅ (by simp))) rowMaskElement 1 u.val n :=
  (Classical.choose_spec (HeckeRowClosure.exists_row_character_with_conductor
    (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

lemma rowCharacter_principal_iff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).residue=1 ↔ (rawRow u).residue=1 :=
  HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (rawRow u) S hS)

lemma supported_coprime_row_fixed (r : O) (hr : Supported (Ideal.span {r})) :
    IsCoprime (Ideal.span {r})
      ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*
        Ideal.span {(72:O)}) := by
  have hl : IsCoprime λ₀ r :=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
      ((supported_span_iff r).mp hr).1
  have hn : IsCoprime (-2:O) r := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff r).mp hr).2)
  have h2 : IsCoprime (2:O) r := hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have h9 : IsCoprime (9:O) r := ShortDraftCRT.nine_coprime_of_not_lambda_dvd r
    ((supported_span_iff r).mp hr).1
  have h72 : IsCoprime (72:O) r := by
    convert (h2.pow_left (m:=3)).mul_left h9 using 1; norm_num
  have hm := (h2.mul_left hl).symm
  have hmod : (fixedSourcePrincipal ∅ (by simp)).modulus=(1:Ideal O) := by
    simp [fixedSourcePrincipal,HeckeRayFamily.character,Character.ofResidue]
  rw [hmod,one_mul]
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hm).mul_right
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr h72.symm)

theorem rawRow_principal_supported_isUnit (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rawRow u).residue=1) : IsUnit u.val := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hu
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hu
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by
    simp [r]
  have hempty : normalizedFactors (Ideal.span {r})=0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro P hP
    have hcop : IsCoprime
        ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)}) P :=
      (supported_coprime_row_fixed r hr).symm.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors hP)
    have hd := HeckeRowNonprincipal.principal_row_multiplicity
      (fixedSourcePrincipal ∅ (by simp)) (rawRow u) rowMaskElement 1 u.val
      (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx (rawRow_elementCoeff u) hp P hP hcop
    have hlt : (normalizedFactors (Ideal.span {r})).count P<6 := by
      rw [hspan]
      exact u.property.2 P
    exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) hlt hd
  have hone : (Ideal.span {u.val}:Ideal O)=1 := by
    rw [←hspan,←Ideal.prod_normalizedFactors_eq_self hr.1,hempty,Multiset.prod_zero]
  exact Ideal.span_singleton_eq_top.mp (by simpa only [Ideal.one_eq_top] using hone)

lemma idealCoeff_principal_eq_one (χ : Character) (hχ : χ.residue=1)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff χ I=1 := by
  change IdealCharacter.value χ.modulus χ.residue I=1
  change IdealCharacter.value χ.modulus χ.residue I≠0 at hI
  unfold IdealCharacter.value at *
  split_ifs at * with hzero
  · exact False.elim (hI rfl)
  · have hu := MulChar.apply_ne_zero_iff.mp hI
    rw [hχ,MulChar.one_apply hu]

theorem rowCharacter_unit_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (v : Oˣ) (hu : u.val=(v:O)) (hv : v≠1) :
    (rowCharacter S hS u).residue≠1 := by
  obtain ⟨P,hmax,hPS,hN,hg,hodd,hval0,hval1⟩ := UnitSexticWitness.exists_unit_witness v hv S 0
  let : P.IsMaximal := hmax
  have hP0 : P≠0 := by
    intro he
    simp [he] at hN
  let Q : PrimeIdeal := ⟨P,Ideal.prime_of_isPrime hP0 hmax.isPrime⟩
  have he : idealCoeff (rowCharacter S hS u) P=idealRowHom (v:O) P := by
    rw [rowCharacter_coeff S hS hbad,highExclusion_prime S hS Q,ite_eq_right hPS,one_mul,hu]
  intro hp
  have hv0 : idealCoeff (rowCharacter S hS u) P≠0 := he ▸ hval0
  exact hval1 (he.symm.trans (idealCoeff_principal_eq_one _ hp P hv0))

theorem rowCharacter_principal_supported_eq_one (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rowCharacter S hS u).residue=1) : u.val=1 := by
  obtain ⟨v,hv⟩ := rawRow_principal_supported_isUnit u hu ((rowCharacter_principal_iff S hS u).mp hp)
  by_contra hn
  have hv1 : v≠1 := by
    intro he
    subst v
    exact hn hv.symm
  exact rowCharacter_unit_nonprincipal S hS hbad u v hv.symm hv1 hp

end SevenEighths.ProbeHighRowFamily

end

end OAI
