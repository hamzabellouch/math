import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandIdentity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothEuler

namespace OAI

/-! The actual smooth Dirichlet series restricted to the typical set.
Finite inclusion-exclusion and the proved smooth Euler formula give the
exact product of nonempty-band Euler factors. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def mrtMaskedCoefficient (F : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) : ℂ :=
  F n * (mrtPrimeMask P n : ℂ)

lemma mrtMaskedCoefficient_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : mrtMaskedCoefficient F P 1 = 1 := by
  simp only [mrtMaskedCoefficient, hF, mrtPrimeMask_one P hP, Complex.ofReal_one, mul_one]

lemma mrtMaskedCoefficient_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    mrtMaskedCoefficient F P (m * n) =
      mrtMaskedCoefficient F P m * mrtMaskedCoefficient F P n := by
  simp only [mrtMaskedCoefficient, hF m n hm hn, mrtPrimeMask_mul P hP,
    Complex.ofReal_mul]
  ring

lemma mrtMaskedCoefficient_oneBounded (F : ℕ → ℂ) (hF : OneBounded F)
    (P : Finset ℕ) : OneBounded (mrtMaskedCoefficient F P) := by
  intro n hn
  by_cases h : mrtPrimeAvoids P n
  · simpa [mrtMaskedCoefficient, mrtPrimeMask, h] using hF n hn
  · simp [mrtMaskedCoefficient, mrtPrimeMask, h]

lemma mrtMaskedCoefficient_term (F : ℕ → ℂ) (P : Finset ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (mrtMaskedCoefficient F P) s n =
      (mrtPrimeMask P n : ℂ) * LSeries.term F s n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, mrtMaskedCoefficient]
  ring

theorem mrt_masked_smooth_euler (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (t : ℝ) :
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term (mrtMaskedCoefficient F P) (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N \ P, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  have hs := (mrt_smooth_euler_product (mrtMaskedCoefficient F P)
    (mrtMaskedCoefficient_one F hF1 P hP) (mrtMaskedCoefficient_mul F hF P hP)
    (mrtMaskedCoefficient_oneBounded F hFb P) N t).2
  have he : (∏ p ∈ primesUpTo N,
      (1 - mrtPrimeEulerTerm (mrtMaskedCoefficient F P) t p)⁻¹) =
      ∏ p ∈ primesUpTo N \ P, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    have hset : primesUpTo N \ P = (primesUpTo N).filter (fun p => p ∉ P) := by
      ext p
      simp
    rw [hset, prod_filter]
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    by_cases hpP : p ∈ P <;>
      simp [mrtPrimeEulerTerm, mrtMaskedCoefficient, mrtPrimeMask_prime P hP hprime, hpP]
  rwa [he] at hs

/-- Exact equation (A.11) before taking norms: the typical smooth series
equals a complement Euler product times the nonempty-band factors. -/
theorem mrt_typical_smooth_euler {ι : Type*} (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, P j ⊆ primesUpTo N) (hdis : Set.PairwiseDisjoint (J : Set ι) P) :
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0)
      ((∏ p ∈ primesUpTo N \ J.biUnion P, (1 - mrtPrimeEulerTerm F t p)⁻¹) *
        ∏ j ∈ J, ((∏ p ∈ P j, (1 - mrtPrimeEulerTerm F t p)⁻¹) - 1)) := by
  have hprime (I : Finset ι) (hI : I ∈ J.powerset) :
      ∀ p ∈ I.biUnion P, p.Prime := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp (hP j (mem_powerset.mp hI hj) hpj)).2
  have hs := hasSum_sum (s := J.powerset) (fun I hI =>
    (mrt_masked_smooth_euler F hF1 hF hFb (I.biUnion P) (hprime I hI) N t).mul_left
      ((-1 : ℂ) ^ I.card))
  have hpoint (n : Nat.smoothNumbers (N + 1)) :
      (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        LSeries.term (mrtMaskedCoefficient F (I.biUnion P))
          (1 + (t : ℂ) * Complex.I) n) =
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0 := by
    have hi : (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        (mrtPrimeMask (I.biUnion P) n : ℂ)) = if mrtTypical J P n then 1 else 0 := by
      have hh := congrArg Complex.ofRealHom (mrtTypical_inclusion_exclusion J P (n : ℕ))
      simpa only [map_sum, map_mul, map_pow, map_neg, map_one, apply_ite, map_zero,
        Complex.ofRealHom_eq_coe] using hh
    simp only [mrtMaskedCoefficient_term, ← mul_assoc, ← sum_mul, hi]
    split_ifs <;> simp
  have hfun : (fun n : Nat.smoothNumbers (N + 1) =>
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        LSeries.term (mrtMaskedCoefficient F (I.biUnion P))
          (1 + (t : ℂ) * Complex.I) n) =
      (fun n : Nat.smoothNumbers (N + 1) => if mrtTypical J P n then
        LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0) := funext hpoint
  rw [hfun] at hs
  convert hs using 1
  exact (mrt_euler_inclusion_exclusion (primesUpTo N) J P
    (fun p => (1 - mrtPrimeEulerTerm F t p)⁻¹) hP hdis).symm

end TwoPointCorrelations

end OAI
