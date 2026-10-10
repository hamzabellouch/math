import Mathlib
import OAI.NumberTheory.PrimePackets.RayFrobenius

namespace OAI

noncomputable section
open Module NumberField Filter Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets

lemma mem_idealsOverPrime_iff (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p ≠ 0) (P : Ideal (𝓞 K)) :
    P ∈ idealsOverPrime K p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp
  rw [idealsOverPrime, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hspan,
    Ideal.span_singleton_le_iff_mem]

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

 

def primeIdealTowerEquiv (p : ℕ) (hp : p ≠ 0) :
    (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) ≃ idealsOverPrime E p := by
  let f : (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) →
      idealsOverPrime E p := fun IQ => by
    refine ⟨IQ.2.val, (mem_idealsOverPrime_iff E hp _).mpr ⟨IQ.2.property.1, ?_⟩⟩
    have hP := ((mem_idealsOverPrime_iff F hp _).mp IQ.1.property).2
    rw [IQ.2.property.2.over] at hP
    simpa only [Ideal.mem_under, map_natCast] using hP
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ he
    have hQ : Q.val = Q'.val := congrArg Subtype.val he
    have hP : P = P' := Subtype.ext (by
      rw [Q.property.2.over, Q'.property.2.over, hQ])
    cases hP
    exact congrArg (Sigma.mk P) (Subtype.ext hQ)
  · intro Q
    have hQ := (mem_idealsOverPrime_iff E hp _).mp Q.property
    let : Q.val.IsPrime := hQ.1
    have hP : Q.val.under (𝓞 F) ∈ idealsOverPrime F p := by
      apply (mem_idealsOverPrime_iff F hp _).mpr
      refine ⟨inferInstance, ?_⟩
      simpa only [Ideal.mem_under, map_natCast] using hQ.2
    refine ⟨⟨⟨Q.val.under (𝓞 F), hP⟩, ⟨Q.val, hQ.1, inferInstance⟩⟩, ?_⟩
    rfl

lemma primeIdealTowerEquiv_val (p : ℕ) (hp : p ≠ 0)
    (PQ : Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) :
    (primeIdealTowerEquiv F E p hp PQ).val = PQ.2.val := rfl

 

def primeIdealEulerFactor (K : Type*) [Field K] [NumberField K] (p : ℕ) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime K p, (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹

lemma primeIdealEulerFactor_eq_pow {p : ℕ} (hp : p ≠ 0) (n : ℕ) (s : ℂ)
    (hc : ∀ P : idealsOverPrime F p, Nat.card (Ideal.primesOver P.val (𝓞 E)) = n)
    (hn : ∀ P : idealsOverPrime F p, ∀ Q : Ideal.primesOver P.val (𝓞 E),
      Ideal.absNorm Q.val = Ideal.absNorm P.val) :
    primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n := by
  let (P : idealsOverPrime F p) : Fintype (Ideal.primesOver P.val (𝓞 E)) :=
    by
      let : P.val.IsPrime := ((mem_idealsOverPrime_iff F hp _).mp P.property).1
      exact (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F E p hp).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma, hn]
  simp only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
  exact Finset.prod_pow _ _ _

lemma dedekindZeta_hasProd (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeIdealEulerFactor K p s) (NumberField.dedekindZeta K s) := by
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have HE := EulerProduct.eulerProduct_hasProd h1 (fun h => hm h) hS h0
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rw [he] at HE
  exact HE.congr_fun (fun p => (ideal_local_complex_euler K hs p.property).symm)

lemma primeEuler_denominator_ne_zero_at_one (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (P : idealsOverPrime K p) :
    1 - (Ideal.absNorm P.val : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
  rw [Complex.cpow_neg_one]
  apply sub_ne_zero.mpr
  intro h
  have he : (Ideal.absNorm P.val : ℂ) = 1 := inv_eq_one.mp h.symm
  have hn : Ideal.absNorm P.val = 1 := by exact_mod_cast he
  have := idealsOverPrime_norm_two_le K P.property
  omega

lemma primeIdealEulerFactor_ne_zero_at_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : primeIdealEulerFactor K p 1 ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact inv_ne_zero (primeEuler_denominator_ne_zero_at_one K P)

lemma primeIdealEulerFactor_continuousAt_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : ContinuousAt (primeIdealEulerFactor K p) 1 := by
  apply tendsto_finsetProd
  intro P _
  exact (continuousAt_const.sub
    (continuousAt_id.neg.const_cpow (Or.inr (by norm_num)))).inv₀
      (primeEuler_denominator_ne_zero_at_one K P)

lemma primeIdealEulerFactor_ne_zero (K : Type*) [Field K] [NumberField K]
    (p : ℕ) {s : ℂ} (hs : 1 < s.re) : primeIdealEulerFactor K p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  apply inv_ne_zero
  intro he
  have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  change ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 at hn
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact (lt_irrefl _ hn)

omit [Algebra F E]

lemma dedekindZeta_ratio_eq_finite_product (n : ℕ) (S : Finset Nat.Primes)
    (hloc : ∀ p : Nat.Primes, p ∉ S → ∀ s : ℂ, 1 < s.re →
      primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s / NumberField.dedekindZeta F s ^ n =
      ∏ p ∈ S, primeIdealEulerFactor E p s / primeIdealEulerFactor F p s ^ n := by
  have HP := (dedekindZeta_hasProd E hs).div₀ ((dedekindZeta_hasProd F hs).pow n)
    (pow_ne_zero n (dedekindZeta_ne_zero_of_one_lt_re F hs))
  rw [← HP.tprod_eq]
  apply tprod_eq_prod
  intro p hp
  rw [hloc p hp s hs, div_self (pow_ne_zero n (primeIdealEulerFactor_ne_zero F p hs))]

 

lemma dedekindZeta_ratio_tendsto_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun s : ℝ => NumberField.dedekindZeta E s /
      NumberField.dedekindZeta F s ^ n) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hE := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT E
  have hF := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have hR : (NumberField.dedekindZeta_residue F : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero F
  have hz : Tendsto (fun s : ℝ => (s : ℂ) - 1) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hc.sub_const 1
  have HT := (hE.div (hF.pow (2 + k)) (pow_ne_zero (2+k) hR)).mul (hz.pow (1+k))
  have HT0 : Tendsto (fun s : ℝ =>
      (((s : ℂ) - 1) * NumberField.dedekindZeta E s /
        (((s : ℂ) - 1) * NumberField.dedekindZeta F s) ^ (2+k)) *
      ((s : ℂ) - 1) ^ (1+k)) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    simpa only [Pi.div_apply, zero_pow (by omega : 1+k ≠ 0), mul_zero] using HT
  apply HT0.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < (s : ℂ).re := hs
  have hd : (s : ℂ) - 1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at he'
    exact (show 1 < s from hs).ne' he'
  have hBF := dedekindZeta_ne_zero_of_one_lt_re F hs'
  simp only [pow_add, pow_one, mul_pow]
  field_simp

 

theorem degree_eq_one_of_localEulerFactor_eq_pow (n : ℕ) (hn : 0 < n)
    (S : Finset Nat.Primes)
    (hloc : ∀ p : Nat.Primes, p ∉ S → ∀ s : ℂ, 1 < s.re →
      primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n) : n = 1 := by
  by_contra hne
  have htwo : 2 ≤ n := by omega
  let C (s : ℂ) := ∏ p ∈ S,
    primeIdealEulerFactor E p s / primeIdealEulerFactor F p s ^ n
  have hC : ContinuousAt C 1 := by
    apply tendsto_finsetProd
    intro p hp
    exact (primeIdealEulerFactor_continuousAt_one E p).div
      ((primeIdealEulerFactor_continuousAt_one F p).pow n)
      (pow_ne_zero n (primeIdealEulerFactor_ne_zero_at_one F p))
  have hCne : C 1 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact div_ne_zero (primeIdealEulerFactor_ne_zero_at_one E p)
      (pow_ne_zero n (primeIdealEulerFactor_ne_zero_at_one F p))
  have H1 : Tendsto (fun s : ℝ => C s) (𝓝[>] 1) (𝓝 (C 1)) :=
    hC.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have HR : Tendsto (fun s : ℝ => NumberField.dedekindZeta E s /
      NumberField.dedekindZeta F s ^ n) (𝓝[>] 1) (𝓝 (C 1)) := by
    apply H1.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (dedekindZeta_ratio_eq_finite_product F E n S hloc (s := s) hs).symm
  exact hCne (tendsto_nhds_unique HR (dedekindZeta_ratio_tendsto_zero F E htwo))

end PrimeDegreePackets

end

end OAI
