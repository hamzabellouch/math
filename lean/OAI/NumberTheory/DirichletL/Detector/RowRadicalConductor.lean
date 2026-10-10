import OAI.NumberTheory.DirichletL.PrimeRows.Conductor
import OAI.NumberTheory.DirichletL.Hecke.LocalRamification

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem canonicalPrimePower_descent (P : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) :
    CenteredMomentCanonical.canonicalPrimePowerCharacter P hg hc x =
      (CompletedGauss.actualSextic P hg ^ c)
        (CenteredMomentCorrelation.primePowerReduction P hc x) := rfl

theorem idealRowHom_congr_radical (I : Ideal O) (x y : O)
    (hxy : x-y ∈ I.radical) : idealRowHom x I = idealRowHom y I := by
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _)
  rw [ite_eq_right hI, ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I.radical ≤ P := hp.radical_le_iff.mpr
    (((Ideal.mem_normalizedFactors_iff hI).mp hP).2)
  unfold localRowValue
  split_ifs with hg
  · let : P.IsMaximal := hg.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

theorem radical_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : I.radical ≠ ⊥ := by
  intro h
  exact hI (bot_unique (h ▸ I.le_radical))

theorem movingNumeratorRow_radical_periodic (r : O)
    (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}).radical
      (movingNumeratorRow r hr) := idealRowHom_congr_radical _

theorem actualPeriodicRow_radical_periodic (Ψ : O →* ℂ) (Q : Ideal O)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ : x-y ∈ Q := Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm : x-y ∈ Ideal.span {m} := Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72 : x-y ∈ Ideal.span {(72 : O)} := Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy : x-y ∈ (Ideal.span {r}).radical := Ideal.mul_le_right hxy
  change ((Ψ x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) *
      movingNumeratorRow r hr x =
    ((Ψ y * coprimalityMask m y) * numeratorBadTwist u a b r hr y) *
      movingNumeratorRow r hr y
  rw [hΨ x y hQ, coprimalityMask_periodic m x y hm,
    numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_radical_periodic r hr x y hrxy]

theorem rowTwist_radical_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _ (actualPeriodicRow (elementHom η) m u a b r hr)
    (actualPeriodicRow_radical_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((supported_span_iff n).mp hs).1 hn
  · exact rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_radical_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical) n) := by
  have hu := rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx hn
  have hle : η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r} ≤
      η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical :=
    Ideal.mul_mono_right (Ideal.span {r}).le_radical
  exact hu.map (Ideal.Quotient.factor hle)

theorem exists_row_character_radical (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {f^4*z}).radical.absNorm ∧
      ∀ n : O, elementCoeff χ n = rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, _, _, _, _⟩ :=
    exists_actual_periodic_row (elementHom η) η.modulus η.modulus_ne_bot
      (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  change f^4*z = (u : O)*λ₀^a*(2 : O)^b*r at hx
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical
  have hM : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (radical_ne_bot _ hr.1)
  have hG := rowTwist_radical_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨HeckeRowClosure.rowCharacter M hM _ hG (rowTwist_unit η m f z), ?_, ?_⟩
  · change M.absNorm ≤ _
    have hfr : Ideal.span {f^4*z} ≤ (Ideal.span {r} : Ideal O) := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
    have hF : (Ideal.span {f^4*z} : Ideal O).radical ≠ ⊥ :=
      radical_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz))
    let : Finite (O ⧸ (Ideal.span {f^4*z} : Ideal O).radical) :=
      Ring.HasFiniteQuotients.finiteQuotient hF
    have hn := FiniteConductor.absNorm_le_of_le (Ideal.radical_mono hfr)
    simpa only [M, map_mul] using Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn
        (rowTwist_nonzero_radical_unit η m f z n hmLam hm2 u a b r hx h)))

theorem periodic_sup (G : O →* ℂ) (I J : Ideal O)
    (hI : CanonicalCoefficientClass.FactorsModulo I G)
    (hJ : CanonicalCoefficientClass.FactorsModulo J G) :
    CanonicalCoefficientClass.FactorsModulo (I ⊔ J) G := by
  intro x y hxy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy
  calc
    G x = G (x-a) := hI _ _ (by convert ha using 1; ring)
    _ = G y := hJ _ _ (by convert hb using 1; linear_combination -hab)

theorem primitive_of_equal_elements (χ θ : Character)
    (hel : ∀ n : O, elementCoeff χ n = elementCoeff θ n) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ θ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  have hθ : CanonicalCoefficientClass.FactorsModulo θ.modulus (elementHom χ) := by
    intro x y hxy
    change elementCoeff χ x = elementCoeff χ y
    rw [hel x, hel y]
    exact elementHom_periodic θ x y hxy
  let M := χ.modulus ⊔ θ.modulus
  have hM : M ≠ ⊥ := fun h => χ.modulus_ne_bot (bot_unique (h ▸ le_sup_left))
  have hG := periodic_sup (elementHom χ) χ.modulus θ.modulus (elementHom_periodic χ) hθ
  have hu : ∀ u : Oˣ, elementHom χ (u : O) = 1 := fun u => χ.unit_trivial u
  let ρ := HeckeRowClosure.rowCharacter M hM (elementHom χ) hG hu
  have hr (n : O) : elementCoeff ρ n = elementCoeff χ n := by
    change elementCoeff (HeckeRowClosure.rowCharacter M hM _ hG hu) n = _
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · have hz : elementCoeff χ n = 0 := by
        by_contra hne
        have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hne
        exact hn (hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left)))
      exact hz.symm
  obtain ⟨ψ, hψ, hp, hn, hmask⟩ := exists_primitive_character ρ
  refine ⟨ψ, le_sup_left.trans hψ, hp, ?_, ?_⟩
  · let : Finite (O ⧸ θ.modulus) := Ring.HasFiniteQuotients.finiteQuotient θ.modulus_ne_bot
    exact hn.trans (FiniteConductor.absNorm_le_of_le (show θ.modulus ≤ M from le_sup_right))
  · intro I
    by_cases hI : I = 0
    · subst I
      simp only [map_zero, ite_self]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn0 : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
    have hre : idealCoeff ρ I = idealCoeff χ I := by
      rw [← hs, idealCoeff_span _ hn0, idealCoeff_span _ hn0, hr]
    by_cases hc : IsCoprime I χ.modulus
    · have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hs.symm ▸ hc)
      have huM : IsUnit (Ideal.Quotient.mk M n) :=
        hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left))
      have hcM : IsCoprime I M := hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp huM
      simpa only [hre, show ρ.modulus = M from rfl, hcM, hc, ite_true] using hmask I
    · rw [ite_eq_right hc]
      simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem rawRow_small_presentation (u : HeckeInverseAmplification.FreeRow) :
    ∃ θ : Character,
      θ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff θ n := by
  obtain ⟨θ, hn, he⟩ := exists_row_character_radical
    (ProbePhysical.fixedSourcePrincipal ∅ (by simp)) ProbeHighRowFamily.rowMaskElement 1 u.val
    ProbeHighRowFamily.rowMaskElement_ne_zero one_ne_zero u.property.1
    (dvd_mul_left _ _) (dvd_mul_right _ _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [ProbeHighRowFamily.conductorConstant, ProbePhysical.fixedSourcePrincipal,
      HeckeRayFamily.character, Character.ofResidue] using hn
  · intro n
    have ho := (Classical.choose_spec
      (exists_row_character_with_conductor (ProbePhysical.fixedSourcePrincipal ∅ (by simp))
        ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
        one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n
    exact ho.trans (he n).symm

theorem rawRow_primitive_radical (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rawRow u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rawRow u) I =
        if IsCoprime I (ProbeHighRowFamily.rawRow u).modulus then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements _ θ he
  exact ⟨ψ, hle, hp, hb.trans hn, hmask⟩

theorem equal_elements_excludePrimes (χ θ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff θ n)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (n : O) :
    elementCoeff (χ.excludePrimes S hS) n = elementCoeff (θ.excludePrimes S hS) n := by
  have hc : IsCoprime (Ideal.span {n}) χ.modulus ↔ IsCoprime (Ideal.span {n}) θ.modulus := by
    have huχ : elementCoeff χ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) χ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    have huθ : elementCoeff θ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) θ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    rw [he n] at huχ
    exact huχ.symm.trans huθ
  simp only [Character.excludePrimes, elementCoeff_refineModulus,
    IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff, hc, he n]

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

theorem rowCharacter_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements
    (ProbeHighRowFamily.rowCharacter S hS u) (θ.excludePrimes S hS)
    (equal_elements_excludePrimes _ θ he S hS)
  refine ⟨ψ, hle, hp, hb.trans ?_, hmask⟩
  change (θ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

theorem prod_le_radical_prod_pow {ι : Type*} (T : Finset ι)
    (P : ι → Ideal O) (e : ι → ℕ) (he : ∀ i ∈ T, 1 ≤ e i) :
    (∏ i ∈ T, P i) ≤ (∏ i ∈ T, P i ^ e i).radical := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hei : e i ≠ 0 := by have := he i (Finset.mem_insert_self i T); omega
    have hpow : (P i ^ e i).radical = (P i).radical := Ideal.radical_pow (P i) hei
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.radical_mul, hpow]
    exact Ideal.mul_le_inf.trans (inf_le_inf (P i).le_radical
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj))))

theorem radical_norm_selected_deficit {ι : Type*} [Fintype ι]
    (I : Ideal O) (hI : I ≠ 0) (P : ι → Ideal O)
    (hP : ∀ i, Prime (P i)) (hdis : Function.Injective P)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (hdiv : ∀ i, P i ^ e i ∣ I) :
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i - 1) ≤ I.absNorm := by
  let (i : ι) : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  have hcop : Pairwise (fun i j => IsCoprime (P i ^ e i) (P j ^ e j)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hdis.ne hij)).pow
  obtain ⟨B, hB⟩ := Fintype.prod_dvd_of_coprime hcop hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    apply hI
    rw [hB, hz, mul_zero]
  have hsmall0 : (∏ i, P i) * B ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne_zero)) hB0
  have hsmall : (∏ i, P i) * B ≤ I.radical := by
    rw [hB, Ideal.radical_mul]
    exact Ideal.mul_le_inf.trans (inf_le_inf
      (prod_le_radical_prod_pow Finset.univ P e (fun i _ => he i)) B.le_radical)
  let : Finite (O ⧸ (∏ i, P i) * B) := Ring.HasFiniteQuotients.finiteQuotient hsmall0
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hprod : (∏ i, P i) * (∏ i, P i ^ (e i-1)) = ∏ i, P i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (he i)
  calc
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
        ((∏ i, P i) * B).absNorm * (∏ i, P i ^ (e i-1)).absNorm := by
      simpa only [map_prod, map_pow] using Nat.mul_le_mul_right
        (∏ i, (P i).absNorm ^ (e i-1)) hn
    _ = I.absNorm := by
      rw [← map_mul]
      congr 1
      calc
        ((∏ i, P i) * B) * (∏ i, P i ^ (e i-1)) =
            ((∏ i, P i) * (∏ i, P i ^ (e i-1))) * B := by ring
        _ = I := by rw [hprod, ← hB]

theorem rowCharacter_primitive_selected_deficit (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          ψ.modulus.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hb := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => (by have := he i; omega)) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i-1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hb

theorem canonicalCRT_radical_congr {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x y : O)
    (hxy : x-y ∈ (∏ i, P i ^ e i).radical) :
    CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) x) =
      CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) y) := by
  rw [CenteredMomentCanonical.canonicalCRTCharacter_mk,
    CenteredMomentCanonical.canonicalCRTCharacter_mk]
  exact idealRowHom_congr_radical _ x y hxy

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

theorem sourceRow_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, ProbePhysical.highExclusion S hS I * idealRowHom u.val I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hn, ?_⟩
  intro I
  rw [← ProbeHighRowFamily.rowCharacter_coeff S hS hbad u I]
  exact hm I

theorem rowCharacter_primitive_selected_div (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          (ψ.modulus.absNorm : ℝ) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) /
              ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
  obtain ⟨ψ, hle, hp, hm, hb⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hpos : 0 < ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hP i).ne_zero)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb k P hP hdis e he hdiv

end SevenEighths.ProbeRowRadicalConductor

end

end OAI
