import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCount
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrincipalDivergence

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

namespace OrdinarySmoothDampedFamily
open Finset OrdinaryCorrelations SourcePrimeFactor Filter

def smoothDamped (f : ℕ → ℂ) (P S : Finset ℕ) (z : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Nat.factoredNumbers S then weightedFunction f P z n else 0

lemma factored_mul_iff (S : Finset ℕ) (m n : ℕ) :
    m*n ∈ Nat.factoredNumbers S ↔
      m ∈ Nat.factoredNumbers S ∧ n ∈ Nat.factoredNumbers S := by
  refine ⟨fun h => ⟨Nat.mem_factoredNumbers_of_dvd h (dvd_mul_right _ _),
    Nat.mem_factoredNumbers_of_dvd h (dvd_mul_left _ _)⟩,
    fun h => Nat.mul_mem_factoredNumbers h.1 h.2⟩

lemma smoothDamped_oneBounded {f : ℕ → ℂ} (hf : OneBounded f)
    (P S : Finset ℕ) {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    OneBounded (smoothDamped f P S z) := by
  intro n
  unfold smoothDamped
  split_ifs
  · exact weightedFunction_oneBounded hf P hz n
  · simp

lemma smoothDamped_multiplicative {f : ℕ → ℂ} (hm : Multiplicative f)
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ) (z : ℝ) :
    Multiplicative (smoothDamped f P S z) := by
  intro m n hm0 hn0 hmn
  simp only [smoothDamped, factored_mul_iff,
    weightedFunction_multiplicative hm hP z m n hm0 hn0 hmn]
  split_ifs <;> simp_all

lemma smoothDamped_one {f : ℕ → ℂ} (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ) (z : ℝ) :
    smoothDamped f P S z 1 = 1 := by
  have he : (P.filter (fun p => p ∣ 1)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (hP p (mem_filter.mp hp).1).ne_one (Nat.eq_one_of_dvd_one (mem_filter.mp hp).2)
  have hc : primeCount P 1 = 0 := by rw [primeCount, he]; rfl
  simp [smoothDamped, Nat.mem_factoredNumbers, weightedFunction, hc, h1]

lemma smooth_distanceSq_lower {f : ℕ → ℂ} (hf : OneBounded f)
    (P S : Finset ℕ) {z : ℝ} (hz : z ∈ Set.Icc 0 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    distanceSq f χ t X / 2 ≤ distanceSq (smoothDamped f P S z) χ t X := by
  open OrdinaryCorrelations.NonpretentiousEuler in
  unfold distanceSq
  rw [sum_div]
  apply sum_le_sum
  intro p hp
  have hrn := twist_norm_le hf χ t p
  have hr : -1 ≤ (twist f χ t p).re ∧ (twist f χ t p).re ≤ 1 := by
    exact ⟨(abs_le.mp ((Complex.abs_re_le_norm _).trans hrn)).1,
      (Complex.re_le_norm _).trans hrn⟩
  by_cases hsm : p ∈ Nat.factoredNumbers S
  · have hd := damping_distance_scalar hr ⟨pow_nonneg hz.1 (primeCount P p),
      pow_le_one₀ hz.1 hz.2⟩
    have he : (smoothDamped f P S z p * star (χ (p : ZMod q) *
        Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re =
        z ^ primeCount P p * (twist f χ t p).re := by
      rw [smoothDamped, ite_eq_left hsm]
      unfold weightedFunction twist
      rw [mul_comm (f p), mul_assoc]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [he]
    convert div_le_div_of_nonneg_right hd (Nat.cast_nonneg p) using 1
    dsimp [twist]
    ring
  · rw [smoothDamped, ite_eq_right hsm, zero_mul, Complex.zero_re, sub_zero]
    convert div_le_div_of_nonneg_right (show (1-(twist f χ t p).re)/2 ≤ 1 by linarith [hr.1])
      (Nat.cast_nonneg p) using 1
    dsimp [twist]
    ring

abbrev Parameters := (Finset ℕ) × (Finset ℕ) × Set.Icc (0:ℝ) 1

def family (f : ℕ → ℂ) (i : Parameters) : ℕ → ℂ :=
  smoothDamped f i.1 i.2.1 i.2.2

theorem family_divergence {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) :
    UniformFamilyHalasz.PrincipalDivergence (family f) := by
  intro R
  filter_upwards [PretentiousEuler.eventual_distanceSq_lower hf hNP 1 (by norm_num)
    (1 : DirichletCharacter ℂ 1) (2*R)] with N hN
  intro i t ht
  have hh := hN t (abs_le.mp ht)
  have hl := smooth_distanceSq_lower hf i.1 i.2.1 i.2.2.2
    (1 : DirichletCharacter ℂ 1) t N
  change R ≤ distanceSq (smoothDamped f i.1 i.2.1 i.2.2) _ t N
  linarith

end OrdinarySmoothDampedFamily

end

end OAI
