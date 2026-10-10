import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.Marks
import OAI.NumberTheory.DirichletL.Descent.Overlap

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem prime_mem_support_iff_dvd (P A : Ideal ActualEisensteinCubic.O)
    (hP : Prime P) (hA : A ≠ 0) :
    P ∈ IdealMobiusDivisorSum.primeSupport A ↔ P ∣ A := by
  simp only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hA, hP, true_and]

theorem ideal_primeMark_eq_divisibility {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P)
    (A : Ideal ActualEisensteinCubic.O) (hA : A ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport A) =
      ∏ i ∈ I, ∑ P ∈ L i, if P ∣ A then a i P else 0 := by
  unfold primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro P hP
  simp only [prime_mem_support_iff_dvd P A (hL i hi P hP) hA]

theorem ideal_primeSupport_mul_cube (n b : Ideal ActualEisensteinCubic.O)
    (hn : n ≠ 0) (hb : b ≠ 0) :
    IdealMobiusDivisorSum.primeSupport (n * b ^ 3) =
      IdealMobiusDivisorSum.primeSupport n ∪ IdealMobiusDivisorSum.primeSupport b := by
  simp only [IdealMobiusDivisorSum.primeSupport,
    normalizedFactors_mul hn (pow_ne_zero 3 hb), normalizedFactors_pow,
    Multiset.toFinset_add]
  congr 1
  ext P
  simp

theorem ideal_whole_mark_priority {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (n b : Ideal ActualEisensteinCubic.O) (hn : n ≠ 0) (hb : b ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport (n * b ^ 3)) =
      ∑ J ∈ I.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport n) *
        primeMark (I \ J) L a
          (IdealMobiusDivisorSum.primeSupport b \ IdealMobiusDivisorSum.primeSupport n) := by
  rw [ideal_primeSupport_mul_cube n b hn hb]
  exact primeMark_priority _ _ _ _ _

theorem ideal_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
      (a : σ → Ideal ActualEisensteinCubic.O → ℂ),
      (I : Set σ).PairwiseDisjoint L →
      (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) →
      ∀ A : Ideal ActualEisensteinCubic.O, A ≠ 0 →
        ‖primeMark I L a (IdealMobiusDivisorSum.primeSupport A)‖ ≤
          C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro σ _ I L a hL ha A hA
  exact (primeMark_norm_le_divisor_count I L a _ hL ha).trans (hb A hA)

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

theorem idealZeroMask_primary_indicator
    (D B : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0)
    (hB : CompletedGauss.primaryGenerator B ≠ 0) :
    CanonicalQuadraticSieve.idealZeroMask D (CompletedGauss.primaryGenerator B) =
      if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {CompletedGauss.primaryGenerator B} =
      Ideal.span {ConcretePrimeRowBridge.idealGenerator B} := by
    rw [(CompletedGauss.primaryGenerator_spec B hB).1,
      ConcretePrimeRowBridge.span_idealGenerator]
  rw [CanonicalQuadraticSieve.idealZeroMask_span_eq D _ _ he,
    CanonicalQuadraticSieve.idealZeroMask_generator_eq_indicator D B hD]

theorem hybrid_quadratic_square_mask
    (k n b c m h t : Ideal ActualEisensteinCubic.O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) := by
  have he : n * b = (c * t) ^ 2 * (m * h) := by rw [hn, hb]; ring
  rw [he, CanonicalQuadraticSieve.canonical_quadraticRow_primary_squarefree k hk,
    idealZeroMask_primary_indicator k (c * t) hk.1 hct]
  rw [isCoprime_comm]

theorem hybrid_double_mask_mobius
    (k P c : Ideal ActualEisensteinCubic.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal ActualEisensteinCubic.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal ActualEisensteinCubic.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := QuadraticSquarefreeKernel.squarefreePart b
  let t := QuadraticSquarefreeKernel.squarePart b
  let c := gcd n g
  let m := CanonicalQuadraticSieve.idealQuotient c n
  let h := CanonicalQuadraticSieve.idealQuotient c g
  have hg : Squarefree g := QuadraticSquarefreeKernel.squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (CanonicalQuadraticSieve.idealQuotient_mul hcn).symm
  have hgh : g = c * h := (CanonicalQuadraticSieve.idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (QuadraticSquarefreeKernel.squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    QuadraticSquarefreeKernel.squarePart_ne_zero hb⟩

theorem ideal_product_fiber_card
    (s t : Finset (Ideal ActualEisensteinCubic.O))
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    (((s ×ˢ t).filter (fun p => p.1 * p.2 = J)).card) ≤ (idealDivisors J).card :=
  CanonicalQuadraticSieve.product_fiber_card (s ×ˢ t) J hJ

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O))
    (B J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end SevenEighths.InverseMoment

end OAI
