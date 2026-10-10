import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedGeometry
import OAI.NumberTheory.DirichletL.Hecke.RowClosure

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass ConcretePrimeRowBridge IdealMobiusDivisorSum
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def deletedPeriod (q:ℕ):ℕ := 2592*q^2

theorem deletedPeriod_ne_zero (q:ℕ)(hq:q≠0):deletedPeriod q≠0 := by
  unfold deletedPeriod
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hq)

theorem fixed_bad_divides_reflection (q:ℕ)(P:Ideal O)(hP:P∈fixedBadPrimes):
    P∣Ideal.span {reflectionConductor q} := by
  change P∈({Ideal.span {goodLambda},Ideal.span {(2:O)}}:Finset (Ideal O)) at hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    have h3:goodLambda∣(3:O):=CubicEisenstein.halfPrimary_lambda_dvd_three
    apply h3.trans
    refine ⟨(864*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring
  · rw [Finset.mem_singleton.mp hP]
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    refine ⟨(1296*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring

theorem excluded_mem_iff (q:ℕ)(hq:q≠0)(P:Ideal O):
    P∈reflectionExcludedPrimes q ↔ Prime P ∧ P∣Ideal.span {reflectionConductor q} := by
  constructor
  · intro hP
    refine ⟨reflectionExcludedPrimes_prime q P hP,?_⟩
    rcases Finset.mem_union.mp hP with hb|hp
    · exact fixed_bad_divides_reflection q P hb
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  · rintro ⟨hp,hd⟩
    exact reflectionConductor_prime_mem q hq P hp hd

theorem excluded_product_divides_reflection (q:ℕ)(hq:q≠0):
    (∏P∈reflectionExcludedPrimes q,P)∣Ideal.span {reflectionConductor q} := by
  apply support_product_dvd (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
  intro P hP
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))).mpr
  obtain ⟨hp,hd⟩:= (excluded_mem_iff q hq P).mp hP
  exact ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩

theorem deleted_reflection_ideal (q:ℕ):
    Ideal.span {reflectionConductor (deletedPeriod q)}=
      (Ideal.span {reflectionConductor q}:Ideal O)^2 := by
  rw [Ideal.span_singleton_pow]
  congr 1
  unfold reflectionConductor deletedPeriod
  push_cast
  ring_nf

theorem deleted_excluded_eq (q:ℕ)(hq:q≠0):
    reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q := by
  ext P
  rw [excluded_mem_iff _ (deletedPeriod_ne_zero q hq),excluded_mem_iff q hq,
    deleted_reflection_ideal]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hp.dvd_of_dvd_pow hd⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hd.trans (dvd_pow_self _ (by decide:2≠0))⟩

theorem deleted_period_ideal (q:ℕ):
    (Ideal.span {(deletedPeriod q:O)}:Ideal O)=
      Ideal.span {(q:O)}*Ideal.span {reflectionConductor q} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold deletedPeriod reflectionConductor
  push_cast
  ring_nf

theorem deleted_period_le_modulus (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    Ideal.span {(deletedPeriod q:O)}≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:O)}≤χ.modulus*(∏P∈reflectionExcludedPrimes q,P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hperiod (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem deleted_element_period (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  intro x y hxy
  apply HeckeRowClosure.elementHom_periodic
  exact deleted_period_le_modulus χ q hq hperiod (Ideal.mul_le_left hxy)

theorem deleted_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖HeckeRowClosure.elementHom
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  exact ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,
    HeckeRowClosure.elementHom_norm _,deleted_element_period χ q hq hperiod⟩

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
