import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic
import OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

theorem logWeight_nonneg (I : Ideal O) : 0≤logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤P.absNorm := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
  have hp : 0<Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, ite_eq_right hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤X → 0≤B →
      (∀ I∈S, (I.absNorm : ℝ)≤X) → (∀ I∈S, ‖f I‖≤B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end SevenEighths.HeckePrimePowers

end

end OAI
