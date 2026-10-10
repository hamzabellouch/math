import OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit
import OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→Finset PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

lemma active_card_le_divisors {k : ℕ} (u : FreeRow) (T : Fin k→Finset PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) :
    (activeChoices u T W Y).card≤(IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card^k := by
  let U : Ideal O := Ideal.span {u.val}
  have hU : U≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  let f : activeChoices u T W Y→(Fin k→IdealMobiusDivisorSum.idealDivisors U) :=
    fun P j=>⟨(P.val j).val.val,(IdealMobiusDivisorSum.mem_idealDivisors hU).mpr
      (((Finset.mem_filter.mp P.property).2 j).1.1)⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g=>(g j).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hc

theorem active_card_subpower (N : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀k : ℕ,k≤N → ∀(u : FreeRow) (T : Fin k→Finset PrimeIdeal)
      (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      ((activeChoices u T W Y).card:ℝ)≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps := by
  let δ := eps/(N+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(max 1 D)^N,by positivity,?_⟩
  intro k hk u T W Y
  have hU : (Ideal.span {u.val}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hU1 : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hd := hdiv (Ideal.span {u.val}) hU
  have hcard : ((activeChoices u T W Y).card:ℝ)≤
      ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := by
    exact_mod_cast active_card_le_divisors u T W Y
  have hpow : D^k≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hke : δ*k≤eps := by
    have hn : (k:ℝ)≤N := by exact_mod_cast hk
    have he : δ*(N+1)=eps := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := hcard
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ)^k := pow_le_pow_left₀ (by positivity) hd k
    _ = D^k*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(δ*k) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    _ ≤ _ := mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le hU1 hke)
      (by positivity) (by positivity)

lemma sum_products_restrict {k : ℕ} (η : Character) (u : FreeRow)
    (T : Fin k→Finset PrimeIdeal) (hT : ∀j P,P∈T j→CanonicalQuadraticSieve.Supported P.val)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) (x w z : ℂ) :
    (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hT j P.val P.property) x w z‖)=
    ∑P∈activeChoices u T W Y,∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u (P j).val (hT j (P j).val (P j).property) x w z‖ := by
  rw [Fintype.prod_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hp
  have hn : ¬∀j,repeatedRowPrime u (P j).val ∧ W j (((P j).val.val.absNorm:ℝ)/Y j)≠0 := by
    simpa only [activeChoices,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_cases hr : repeatedRowPrime u (P j).val
  · simp [hj hr]
  · simp [centralRepeatedTerm,hr]
end SevenEighths.ProbeCentralRepeatedChoices

end

end OAI
