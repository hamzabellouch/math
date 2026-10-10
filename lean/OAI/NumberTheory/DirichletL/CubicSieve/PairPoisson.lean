import OAI.NumberTheory.DirichletL.CubicSieve.PairPrimes

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrincipalRow (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : O ⧸ Ideal.span {primaryGenerator I * primaryGenerator J} → ℂ :=
  principalSexticRow (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) (primaryGenerator I * primaryGenerator J)
    (pairPrime_modulus I J hI hJ)

lemma pairPrincipalRow_mk (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (z : O) :
    pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) =
      star (cubicRow I z) * cubicRow J z := by
  unfold pairPrincipalRow
  rw [principalSexticRow_mk (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) _ (pairPrime_modulus I J hI hJ) z,
    pairPrime_row I J hI hJ]

lemma pairPrincipalGauss_eq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = cubicPairGauss I J hI hJ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ Ideal.span {a * b}) := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (O ⧸ Ideal.span {a * b}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span hI.2
  let e : (O ⧸ Ideal.span {a * b}) ≃+* (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) = (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul, Complex.ofReal_mul]
  dsimp only [principalNormalizedGauss, cubicPairGauss]
  rw [hnorm]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  change pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) * _ = _
  rw [pairPrincipalRow_mk]
  simp only [e, a, b, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]
  rw [← MulChar.star_apply', principalCubicCharacter_mk I hI, principalCubicCharacter_mk J hJ]
  congr 1

lemma pairPrincipalGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  rw [pairPrincipalGauss_eq I J hI hJ hcop, cubicPairGauss_separation I J hI hJ hcop]

theorem cubic_pair_poisson (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, (star (cubicRow I z) * cubicRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        (‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ : ℂ)) *
      ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2) := by
  let c := primaryGenerator I * primaryGenerator J
  have hc0 : c ≠ 0 := mul_ne_zero hI.2 hJ.2
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (pairPrime_modulus I J hI hJ)
  let : Fintype (O ⧸ ∏ P, pairPrime I J P) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (P : PrimeIndex I ⊕ PrimeIndex J) : Fintype (O ⧸ pairPrime I J P) := Fintype.ofFinite _
  let row := pairPrincipalRow I J hI hJ hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  let G := ∑ r : O ⧸ Ideal.span {c}, row r * ψ r
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        (cubicRow I h * star (cubicRow J h)) * G := by
    have hh := canonical_principal_gauss_transform_of_nontrivial (pairPrime I J)
      (pairPrime_coprime I J hI hJ hcop) (pairPrime_good I J hI hJ) (pairExponent I J)
      (pairExponent_nonprincipal I J hI hJ) c (pairPrime_modulus I J hI hJ) ψ
      (Ideal.Quotient.mk (Ideal.span {c}) h)
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (row (Ideal.Quotient.mk (Ideal.span {c}) h)) * G at hh
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ h)) * G at hh
    rw [pairPrincipalRow_mk I J hI hJ hcop h, star_mul, star_star,
      mul_comm (star (cubicRow J h)) (cubicRow I h)] at hh
    exact hh
  have hp := actual_radial_paper_poisson_trace W M hM c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      (M / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  have hsum : (∑' h : O, ((cubicRow I h * star (cubicRow J h)) * G) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hsum] at hp
  have hrow (z : O) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      star (cubicRow I z) * cubicRow J z :=
    pairPrincipalRow_mk I J hI hJ hcop z
  simp_rw [hrow] at hp
  rw [hp]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc0))
  have hGauss := pairPrincipalGauss_separation I J hI hJ hcop
  change G / (‖eisEmbedding c‖ : ℂ) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * _) = _
  rw [← mul_assoc]
  congr 1
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * G =
    (M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (‖eisEmbedding c‖ : ℂ)
  rw [hG]
  push_cast
  field_simp [hn]

end
end SevenEighths.CubicSieve

end OAI
