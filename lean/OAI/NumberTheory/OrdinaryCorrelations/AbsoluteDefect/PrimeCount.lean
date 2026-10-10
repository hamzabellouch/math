import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormOneAddLeExp

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open Finset

def primeCount (P : Finset ℕ) (n : ℕ) : ℕ := (P.filter (fun p => p ∣ n)).card

lemma primeCount_coprime_mul {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {m n : ℕ} (hmn : m.Coprime n) :
    primeCount P (m*n) = primeCount P m + primeCount P n := by
  have he : P.filter (fun p => p ∣ m*n) =
      (P.filter (fun p => p ∣ m)) ∪ (P.filter (fun p => p ∣ n)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp, hdiv⟩
      exact ((hP p hp).dvd_mul.mp hdiv).elim (fun h => Or.inl ⟨hp,h⟩)
        (fun h => Or.inr ⟨hp,h⟩)
    · rintro (⟨hp,hm⟩ | ⟨hp,hn⟩)
      · exact ⟨hp, dvd_mul_of_dvd_left hm n⟩
      · exact ⟨hp, dvd_mul_of_dvd_right hn m⟩
  have hd : Disjoint (P.filter (fun p => p ∣ m)) (P.filter (fun p => p ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hdiv : p ∣ 1 := hmn.gcd_eq_one ▸ Nat.dvd_gcd (mem_filter.mp hp).2 (mem_filter.mp hq).2
    exact (hP p (mem_filter.mp hp).1).ne_one (Nat.eq_one_of_dvd_one hdiv)
  simp only [primeCount, he, card_union_of_disjoint hd]

def weightedFunction (f : ℕ → ℂ) (P : Finset ℕ) (z : ℝ) (n : ℕ) : ℂ :=
  f n * ((z ^ primeCount P n : ℝ) : ℂ)

lemma weightedFunction_multiplicative {f : ℕ → ℂ}
    (hf : OrdinaryCorrelations.Multiplicative f) {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℝ) :
    OrdinaryCorrelations.Multiplicative (weightedFunction f P z) := by
  intro m n hm hn hmn
  simp only [weightedFunction, hf m n hm hn hmn, primeCount_coprime_mul hP hmn,
    pow_add, Complex.ofReal_mul]
  ring

lemma weightedFunction_oneBounded {f : ℕ → ℂ}
    (hf : OrdinaryCorrelations.OneBounded f) (P : Finset ℕ)
    {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    OrdinaryCorrelations.OneBounded (weightedFunction f P z) := by
  intro n
  rw [weightedFunction, norm_mul, Complex.norm_of_nonneg (pow_nonneg hz.1 _)]
  exact (mul_le_of_le_one_left (pow_nonneg hz.1 _) (hf n)).trans (pow_le_one₀ hz.1 hz.2)

lemma damping_distance_scalar {r w : ℝ} (hr : -1 ≤ r ∧ r ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1) : (1-r)/2 ≤ 1-w*r := by
  by_cases h : 0 ≤ r
  · have hwr := mul_le_mul_of_nonneg_right hw.2 h
    nlinarith
  · have hwr := mul_nonpos_of_nonneg_of_nonpos hw.1 (le_of_not_ge h)
    linarith

lemma weighted_distanceSq_lower {f : ℕ → ℂ}
    (hf : OrdinaryCorrelations.OneBounded f) (P : Finset ℕ)
    {z : ℝ} (hz : z ∈ Set.Icc 0 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    OrdinaryCorrelations.distanceSq f χ t X / 2 ≤
      OrdinaryCorrelations.distanceSq (weightedFunction f P z) χ t X := by
  open OrdinaryCorrelations OrdinaryCorrelations.NonpretentiousEuler in
  unfold distanceSq
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hrn := twist_norm_le hf χ t p
  have hr : -1 ≤ (twist f χ t p).re ∧ (twist f χ t p).re ≤ 1 := by
    constructor
    · have hh := (abs_le.mp ((Complex.abs_re_le_norm (twist f χ t p)).trans hrn)).1
      exact hh
    · exact (Complex.re_le_norm _).trans hrn
  have hd := damping_distance_scalar hr ⟨pow_nonneg hz.1 (primeCount P p),
    pow_le_one₀ hz.1 hz.2⟩
  have he : (weightedFunction f P z p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re =
      z ^ primeCount P p * (twist f χ t p).re := by
    unfold weightedFunction twist
    rw [mul_comm (f p), mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he]
  convert div_le_div_of_nonneg_right hd (Nat.cast_nonneg p) using 1
  dsimp [twist]
  ring

lemma weighted_distance_lower {f : ℕ → ℂ}
    (hf : OrdinaryCorrelations.OneBounded f) (P : Finset ℕ)
    {z : ℝ} (hz : z ∈ Set.Icc 0 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    OrdinaryCorrelations.distance f χ t X / 2 ≤
      OrdinaryCorrelations.distance (weightedFunction f P z) χ t X := by
  open OrdinaryCorrelations OrdinaryCorrelations.NonpretentiousEuler in
  have h1 := distanceSq_nonneg hf χ t X
  have h2 := distanceSq_nonneg (weightedFunction_oneBounded hf P hz) χ t X
  have hd := weighted_distanceSq_lower hf P hz χ t X
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  have hn1 := Real.sqrt_nonneg (distanceSq f χ t X)
  have hn2 := Real.sqrt_nonneg (distanceSq (weightedFunction f P z) χ t X)
  unfold distance
  nlinarith

theorem eventual_all_weighted_distance {f : ℕ → ℂ}
    (hf : OrdinaryCorrelations.OneBounded f)
    (hNP : OrdinaryCorrelations.UniformlyNonpretentious f)
    (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q) (R : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (P : Finset ℕ) (z : ℝ), z ∈ Set.Icc 0 1 →
      ∀ t : ℝ, t ∈ Set.Icc (-(N:ℝ)) (N:ℝ) →
      R ≤ OrdinaryCorrelations.distance (weightedFunction f P z) χ t (N:ℝ) := by
  open OrdinaryCorrelations in
  have hmin := (hNP q hq χ).eventually (Filter.eventually_ge_atTop (2*R))
  filter_upwards [hmin] with N hN
  intro P z hz t ht
  have hb : BddBelow ((fun t : ℝ => distance f χ t (N:ℝ)) ''
      Set.Icc (-(N:ℝ)) (N:ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact Real.sqrt_nonneg _
  have hd := hN.trans (csInf_le hb (Set.mem_image_of_mem _ ht))
  exact (by linarith : R ≤ distance f χ t (N:ℝ)/2).trans
    (weighted_distance_lower hf P hz χ t (N:ℝ))

lemma cofactor_integral (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    (∫ z in Set.Icc (0:ℝ) 1, weightedFunction f P z n) =
      f n / (primeCount P n + 1 : ℂ) := by
  unfold weightedFunction
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]
  have hi : (∫ z in Set.Icc (0:ℝ) 1, z ^ primeCount P n) = (1:ℝ)/(primeCount P n + 1) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
    simp
  rw [hi]
  simp [div_eq_mul_inv]

end SourcePrimeFactor

end

end OAI
