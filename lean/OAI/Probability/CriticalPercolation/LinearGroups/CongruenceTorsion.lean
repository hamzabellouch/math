import Mathlib
import OAI.Probability.CriticalPercolation.Growth.PolynomialGrowthDescent

namespace OAI

section
noncomputable section
open Set Function
open scoped BigOperators

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [CommRing R]

lemma one_add_pow_of_sq_zero {B : Type*} [Ring B] (b : B) (hb : b*b=0) (q : ℕ) :
    (1+b)^q=1+q•b := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ,ih,add_mul,one_mul,smul_mul_assoc,mul_add,mul_one,hb,add_zero,
      add_nsmul,one_nsmul]
    abel

lemma scalar_inverse_mod (I : Ideal R) [I.IsMaximal] (q : ℕ) (hq : (q:R)∉I) :
    ∃ r : R, 1-r*(q:R)∈I := by
  let := Ideal.Quotient.field I
  have hqn : Ideal.Quotient.mk I (q:R)≠0 := by exact mt Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk I (q:R))⁻¹)
  refine ⟨r,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub,map_one,map_mul,hr,inv_mul_cancel₀ hqn,sub_self]

lemma congruence_power_step {n : Type*} [Fintype n] [DecidableEq n]
    (I : Ideal R) [I.IsMaximal] (A : Matrix n n R) (k q : ℕ)
    (hk : 1≤k) (hq : (q:R)∉I) (hpow : A^q=1)
    (hA : ∀ i j, (A-1) i j∈I^k) : ∀ i j, (A-1) i j∈I^(k+1) := by
  let J := I^(k+1)
  let f := (Ideal.Quotient.mk J).mapMatrix (m:=n)
  let B := A-1
  have hsquare : f (B*B)=0 := by
    ext i j
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (∑ l, B i l*B l j)∈I^(k+1)
    apply Ideal.sum_mem
    intro l hl
    apply Ideal.pow_le_pow_right (show k+1≤k+k by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul (hA i l) (hA l j)
  have hsquare' : f B*f B=0 := by simpa using hsquare
  have hsum : 1+q•f B=1 := by
    rw [←one_add_pow_of_sq_zero (f B) hsquare']
    have he : 1+f B=f A := by dsimp only [B]; rw [map_sub,map_one]; abel
    rw [he,←map_pow,hpow,map_one]
  have hz : q•f B=0 := add_left_cancel (hsum.trans (add_zero _).symm)
  have hqB (i j) : (q:R)*B i j∈J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun M : Matrix n n (R ⧸ J) => M i j) hz
    simpa [f,nsmul_eq_mul,map_mul] using he
  obtain ⟨r,hr⟩ := scalar_inverse_mod I q hq
  intro i j
  have h1 := J.mul_mem_left r (hqB i j)
  have h2 : (1-r*(q:R))*B i j∈J := by
    change _∈I^(k+1)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hr (hA i j)
  have h := J.add_mem h1 h2
  convert h using 1; ring

lemma eq_one_of_prime_to_residue_order {n : Type*} [Fintype n] [DecidableEq n]
    [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsMaximal]
    (A : Matrix n n R) (q : ℕ) (hq : (q:R)∉I) (hpow : A^q=1)
    (hA : ∀ i j, (A-1) i j∈I) : A=1 := by
  have hall (k : ℕ) : ∀ i j, (A-1) i j∈I^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hk : k=0
      · simpa [hk] using hA
      · exact congruence_power_step I A k q (by omega) hq hpow ih
  have he (i j) : (A-1) i j=0 := by
    have hm : (A-1) i j∈⨅ k : ℕ, I^k := by simpa using (fun k => hall k i j)
    rw [Ideal.iInf_pow_eq_bot_of_isDomain I (Ideal.IsMaximal.ne_top inferInstance)] at hm
    exact hm
  exact sub_eq_zero.mp (Matrix.ext he)

lemma int_isJacobsonRing : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hP0 : P=⊥
  · subst P
    apply le_antisymm _ Ideal.le_jacobson
    intro x hx
    obtain ⟨z,hz⟩ := Ideal.mem_jacobson_iff.mp hx (3*x)
    change z*(3*x)*x+z-1=0 at hz
    have hu : IsUnit (3*x*x+1) := ⟨⟨3*x*x+1,z,by nlinarith [hz],by nlinarith [hz]⟩,rfl⟩
    rcases Int.isUnit_iff.mp hu with h|h <;> change x=0 <;> nlinarith [sq_nonneg x]
  · let : P.IsPrime := hP
    let : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

lemma finite_field_of_finiteType_int (F : Type*) [Field F] [a : Algebra ℤ F] [Algebra.FiniteType ℤ F] :
    Finite F := by
  cases Subsingleton.elim a (Ring.toIntAlgebra F)
  let : IsJacobsonRing ℤ := int_isJacobsonRing
  let : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  let J : Ideal ℤ := Ideal.under ℤ (⊥ : Ideal F)
  have hJ : J.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (⊥ : Ideal F)
  have hJ0 : J≠⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hJ Int.not_isField
  let : Finite (ℤ ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ0
  let : Module.Finite (ℤ ⧸ J) (F ⧸ (⊥ : Ideal F)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  let : Finite (F ⧸ (⊥ : Ideal F)) := Module.finite_of_finite (ℤ ⧸ J)
  exact Finite.of_injective (Ideal.Quotient.mk (⊥ : Ideal F)) (by
    intro x y h
    exact sub_eq_zero.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp h))

lemma finite_residue_of_finiteType_int [Algebra.FiniteType ℤ R]
    (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := by
  let := Ideal.Quotient.field I
  let : Algebra.FiniteType ℤ (R ⧸ I) := Algebra.FiniteType.quotient ℤ I
  exact finite_field_of_finiteType_int (R ⧸ I)

lemma exists_maximal_avoiding [IsDomain R] [IsJacobsonRing R] (x : R) (hx : x≠0) :
    ∃ I : Ideal R, I.IsMaximal ∧ x∉I := by
  by_contra! h
  have hm : x∈(⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson,Submodule.mem_sInf]
    exact fun I hI => h I hI.2
  rw [IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)] at hm
  exact hx hm

end CriticalPercolation.LinearGrowth
end
end

end OAI
