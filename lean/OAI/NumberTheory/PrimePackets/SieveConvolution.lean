import Mathlib
import OAI.NumberTheory.PrimePackets.PenaltyEuler

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma convolution_prime {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) : (f*g) p = f 1 * g p + f p * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  rw [hp.sum_divisors]
  simp [Nat.div_self hp.pos, add_comm]

lemma convolution_pow_prime {R : Type*} [CommSemiring R] (f : ArithmeticFunction R)
    (h1 : f 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) : (f^k) p = k * f p := by
  induction k with
  | zero => simp [hp.ne_one]
  | succ k ih =>
    rw [pow_succ, convolution_prime _ _ hp, ih]
    have hk1 : (f^k) 1 = 1 := by
      clear ih
      induction k with
      | zero => simp
      | succ k ih => simp only [pow_succ, ArithmeticFunction.mul_apply_one, ih, h1, one_mul]
    rw [hk1, h1]
    push_cast
    ring

lemma nFoldDivisor_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    nFoldDivisor k p = k := by
  unfold nFoldDivisor
  rw [convolution_pow_prime _ (by simp) hp]
  simp [ArithmeticFunction.zeta_apply, hp.ne_zero]

lemma mul_le_of_prime_power_le (f g : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (h : ∀ p j, p.Prime → f (p^j) ≤ g (p^j)) (m : ℕ) :
    f m ≤ g m := by
  by_cases hm : m = 0
  · simp [hm]
  rw [hf.multiplicative_factorization f hm, hg.multiplicative_factorization g hm]
  apply Finset.prod_le_prod₀
  · intro p _
    exact hf0 _
  · intro p hp
    exact h p _ (Nat.prime_of_mem_primeFactors hp)

 

def coefficientPenalty (k : ℕ) (b : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  if p.Prime then b p / (k+1) else 0

lemma coefficientPenalty_bounds (k : ℕ) (b : ArithmeticFunction ℝ)
    (hb : ∀m, 0 ≤ b m ∧ b m ≤ nFoldDivisor (k+1) m) (p : ℕ) :
    0 ≤ coefficientPenalty k b p ∧ coefficientPenalty k b p ≤ 1 := by
  unfold coefficientPenalty
  split_ifs with hp
  · constructor
    · exact div_nonneg (hb p).1 (by positivity)
    · apply (div_le_one (by positivity : (0:ℝ) < k+1)).mpr
      simpa [nFoldDivisor_prime _ hp] using (hb p).2
  · exact ⟨le_rfl, zero_le_one⟩

lemma coefficientPenalty_prime (k : ℕ) (b : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (k+1 : ℝ) * coefficientPenalty k b p = b p := by
  simp only [coefficientPenalty, ite_eq_left hp]
  have hk : (k+1:ℝ) ≠ 0 := by positivity
  field_simp

lemma convolution_ge_left (f g : ArithmeticFunction ℝ) (hf : ∀m, 0 ≤ f m)
    (hg : ∀m, 0 ≤ g m) (hg1 : g 1 = 1) {m : ℕ} (hm : m ≠ 0) :
    f m ≤ (f*g) m := by
  rw [ArithmeticFunction.mul_apply]
  have hd : (m,1) ∈ m.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hm⟩
  simpa [hg1] using Finset.single_le_sum (fun de _ => mul_nonneg (hf de.1) (hg de.2)) hd

 

theorem divisor_bounded_majorant (k : ℕ) (b : ArithmeticFunction ℝ)
    (hmult : b.IsMultiplicative) (hb : ∀m, 0 ≤ b m ∧ b m ≤ nFoldDivisor (k+1) m)
    (m : ℕ) :
    b m ≤ (powerfulFunction k * (primePenalty (coefficientPenalty k b))^(k+1)) m := by
  let f := primePenalty (coefficientPenalty k b)
  have hf : f.IsMultiplicative := primePenalty_multiplicative _
  have hf0 : ∀m, 0 ≤ f m := primePenalty_nonneg _ (fun p => (coefficientPenalty_bounds k b hb p).1)
  have hF0 : ∀m, 0 ≤ (f^(k+1)) m := convolution_pow_nonneg hf0 _
  have hP0 : ∀m, 0 ≤ powerfulFunction k m := powerfulCorrection_nonneg k
  apply mul_le_of_prime_power_le b _ hmult ((powerfulFunction_multiplicative k).mul hf.pow)
    (fun m => (hb m).1) _ m
  intro p j hp
  by_cases hj0 : j=0
  · simp [hj0, hmult.map_one, ((powerfulFunction_multiplicative k).mul hf.pow).map_one]
  by_cases hj1 : j=1
  · have hfprime : (f^(k+1)) p = b p := by
      rw [convolution_pow_prime _ hf.map_one hp]
      have hp1 : f p = coefficientPenalty k b p := by
        simpa only [pow_one] using primePenalty_prime_pow (coefficientPenalty k b) hp (by omega : 1 ≠ 0)
      rw [hp1]
      simpa using coefficientPenalty_prime k b hp
    rw [hj1, pow_one]
    rw [mul_comm]
    rw [← hfprime]
    exact convolution_ge_left _ _ hF0 hP0 (powerfulCorrection_one k) hp.ne_zero
  · have hj2 : 2 ≤ j := by omega
    calc
      b (p^j) ≤ (nFoldDivisor (k+1) (p^j) : ℝ) := (hb _).2
      _ = powerfulFunction k (p^j) := by
        simp [powerfulFunction_apply, powerfulCorrection, isPowerful_prime_pow hp hj2]
      _ ≤ (powerfulFunction k * f^(k+1)) (p^j) :=
        convolution_ge_left _ _ hP0 hF0 hf.pow.map_one (pow_ne_zero _ hp.ne_zero)

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma nFoldDivisor_real (k m : ℕ) :
    (nFoldDivisor k m : ℝ) = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) m := by
  induction k generalizing m with
  | zero => simp [nFoldDivisor, ArithmeticFunction.one_apply]
  | succ k ih =>
    rw [nFoldDivisor_succ, pow_succ, ArithmeticFunction.coe_mul_zeta_apply]
    push_cast
    exact Finset.sum_congr rfl (fun d _ => ih d)

lemma primePenalty_pow_le_divisor (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1) (k m : ℕ) :
    ((primePenalty g)^k) m ≤ nFoldDivisor k m := by
  rw [nFoldDivisor_real]
  induction k generalizing m with
  | zero => exact le_rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_le_sum
    intro de hde
    have he0 : de.2 ≠ 0 := by
      obtain ⟨hm, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hde
      intro h; simp_all
    apply mul_le_mul (ih de.1) _ (primePenalty_nonneg g (fun p => (hg p).1) de.2)
      (by rw [← nFoldDivisor_real]; positivity)
    simpa [ArithmeticFunction.zeta_apply, he0] using primePenalty_le_one g hg de.2

lemma convolution_sum_interval (f g : ArithmeticFunction ℝ) (a b : ℕ) :
    (∑ m ∈ Finset.Ioc a b, (f*g) m) =
      ∑ d ∈ Finset.Icc 1 b, g d * ∑ e ∈ Finset.Ioc (a/d) (b/d), f e := by
  have hdiv : ∀ m : ℕ, m.divisors.filter (0 < ·) = m.divisors := by
    intro m
    exact Finset.filter_eq_self.mpr (fun d hd => Nat.pos_of_mem_divisors hd)
  have hint : ∀ d : ℕ, (Finset.Ioc (a/d) (b/d)).filter (0 < ·) = Finset.Ioc (a/d) (b/d) := by
    intro d
    apply Finset.filter_eq_self.mpr
    intro e he
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp he).1
  simp only [ArithmeticFunction.mul_apply]
  simp_rw [Nat.sum_divisorsAntidiagonal (fun u v => f u * g v)]
  have hid := sum_divisor_large_interval (fun u v => f u * g v) a b 0
  simp only [hdiv, hint, zero_add, Nat.div_one] at hid
  rw [hid]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul, mul_comm]

lemma primePenalty_pow_initial_le (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1) (k N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g)^(k+1)) m) ≤
      (N:ℝ) * (1 + Real.log N)^k := by
  apply (Finset.sum_le_sum (fun m _ => primePenalty_pow_le_divisor g hg (k+1) m)).trans
  exact nFoldDivisor_summatory_le k N

lemma primePenalty_pow_interval_trivial (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1)
    (k a b d : ℕ) (hd : 0 < d) :
    (∑ m ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) m) ≤
      ((b:ℝ)/d) * (1 + Real.log b)^k := by
  have hf0 := convolution_pow_nonneg (primePenalty_nonneg g (fun p => (hg p).1)) (k+1)
  have hsub : Finset.Ioc (a/d) (b/d) ⊆ Finset.Icc 1 (b/d) := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (a/d)).trans_lt (Finset.mem_Ioc.mp hm).1), (Finset.mem_Ioc.mp hm).2⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hf0 m)).trans
  apply (primePenalty_pow_initial_le g hg k (b/d)).trans
  by_cases hq : b/d = 0
  · simp only [hq, Nat.cast_zero, zero_mul]
    have hlog : 0 ≤ 1 + Real.log (b:ℝ) := by
      by_cases hb : b=0
      · simp [hb]
      have hl : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg (show (1:ℝ) ≤ b by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb)
      linarith
    positivity
  have hq1 : (1:ℝ) ≤ (b/d:ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hq0 : (0:ℝ) < (b/d:ℕ) := lt_of_lt_of_le zero_lt_one hq1
  apply mul_le_mul Nat.cast_div_le _ (pow_nonneg (by linarith [Real.log_nonneg hq1]) _) (by positivity)
  apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hq1])
  linarith only [Real.log_le_log hq0 (show ((b/d:ℕ):ℝ) ≤ (b:ℝ) by exact_mod_cast Nat.div_le_self b d)]

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma divided_interval_estimates (a b d T : ℕ) (η : ℝ)
    (hab : a ≤ b) (hd : 0 < d) (hdT : d ≤ T) (hT : 2 ≤ T)
    (hTb : T^2 ≤ b) (hbT : b ≤ T^4) (hη : 0 < η)
    (hηT : 2 ≤ η*T) (hrel : η*b ≤ (b:ℝ)-a) :
    T ≤ b/d ∧ a/d ≤ b/d ∧
      (η/2) * (b/d:ℕ) ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) ∧
      (0 < Real.log b) ∧ (0 < Real.log (b/d:ℕ)) ∧
      (((b/d:ℕ):ℝ)-(a/d:ℕ))/Real.log (b/d:ℕ) ≤
        8 * (((b:ℝ)-a)/Real.log b) / d := by
  have hTu : T ≤ b/d := (Nat.le_div_iff_mul_le hd).mpr <|
    (Nat.mul_le_mul_left T hdT).trans (by simpa [pow_two] using hTb)
  have hdu : (0:ℝ) < d := by exact_mod_cast hd
  have hTc : (2:ℝ) ≤ T := by exact_mod_cast hT
  have hTuc : (T:ℝ) ≤ (b/d:ℕ) := by exact_mod_cast hTu
  have hU : ((b/d:ℕ):ℝ) ≤ (b:ℝ)/d := Nat.cast_div_le
  have hA : ((a/d:ℕ):ℝ) ≤ (a:ℝ)/d := Nat.cast_div_le
  have hU' := real_div_lt_nat_div_add_one b hd
  have hlen := interval_div_length_le a b d hd
  have hy : η * ((b:ℝ)/d) ≤ ((b:ℝ)-a)/d := by
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right hrel hdu.le
  have het : (2:ℝ) ≤ η * ((b/d:ℕ):ℝ) :=
    hηT.trans (mul_le_mul_of_nonneg_left hTuc hη.le)
  have het' : (2:ℝ) ≤ ((b:ℝ)-a)/d :=
    (het.trans (mul_le_mul_of_nonneg_left hU hη.le)).trans hy
  have hlow : η * ((b/d:ℕ):ℝ)-1 ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) := by
    have hηU := mul_le_mul_of_nonneg_left hU hη.le
    have hdiv : ((b:ℝ)-a)/d = (b:ℝ)/d-(a:ℝ)/d := sub_div _ _ _
    linarith
  have hrelative : (η/2)*((b/d:ℕ):ℝ) ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) := by linarith
  have hupper : ((b/d:ℕ):ℝ)-(a/d:ℕ) ≤ 2*(((b:ℝ)-a)/d) := by linarith
  have hb2 : 1 < b := by nlinarith
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb2)
  have hlogu : 0 < Real.log (b/d:ℕ) := Real.log_pos (by linarith)
  have hlogT : Real.log b ≤ 4 * Real.log T := by
    have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have ht0 : (0:ℝ) < T := by linarith
    have h := Real.log_le_log hb0 (show (b:ℝ) ≤ (T:ℝ)^4 by exact_mod_cast hbT)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogTu : Real.log T ≤ Real.log (b/d:ℕ) := Real.log_le_log (by linarith) hTuc
  have hlog : Real.log b / 4 ≤ Real.log (b/d:ℕ) := by linarith
  refine ⟨hTu, Nat.div_le_div_right hab, hrelative, hlogb, hlogu, ?_⟩
  calc
    _ ≤ (2*(((b:ℝ)-a)/d))/(Real.log b/4) :=
      div_le_div₀ (by linarith only [hupper, het']) hupper (by positivity) hlog
    _ = _ := by ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

def intervalConstant (k : ℕ) : ℝ :=
  (((12*(k+1)+2:ℕ):ℝ) * (2*((k+1:ℕ):ℝ)+1) * Real.exp (k+1))

lemma intervalConstant_nonneg (k : ℕ) : 0 ≤ intervalConstant k := by unfold intervalConstant; positivity

def primeExponential (g : ℕ → ℝ) (k b : ℕ) : ℝ :=
  Real.exp (∑ p ∈ smallPrimes b, ((k+1:ℕ):ℝ) * g p / p)

lemma primeExponential_one_le (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p) (k b : ℕ) :
    1 ≤ primeExponential g k b := by
  apply Real.one_le_exp_iff.mpr
  exact Finset.sum_nonneg (fun p _ => div_nonneg (mul_nonneg (by positivity) (hg p)) (Nat.cast_nonneg p))

lemma primeExponential_mono (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p) (k : ℕ)
    {a b : ℕ} (hab : a ≤ b) : primeExponential g k a ≤ primeExponential g k b := by
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hab)
  · intro p _ _
    exact div_nonneg (mul_nonneg (by positivity) (hg p)) (Nat.cast_nonneg p)

 

theorem corrected_interval_finite (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b T : ℕ, a ≤ b → 2 ≤ T → B ≤ T → T^2 ≤ b → b ≤ T^4 →
      2 ≤ η*T → η*b ≤ (b:ℝ)-a →
      (∑ m ∈ Finset.Ioc a b, (powerfulFunction k * (primePenalty g)^(k+1)) m) ≤
        8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k := by
  obtain ⟨B, hB⟩ := primePenalty_pow_relative_interval k (η/2) (by positivity)
  refine ⟨B, ?_⟩
  intro g hg a b T hab hT hBT hTb hbT hηT hrel
  have hg0 : ∀p, 0 ≤ g p := fun p => (hg p).1
  have hf0 : ∀m, 0 ≤ ((primePenalty g)^(k+1)) m := convolution_pow_nonneg (primePenalty_nonneg g hg0) _
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hb0 : (0:ℝ) < b := by exact_mod_cast (show 0 < b by nlinarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by nlinarith))
  have hy : 0 ≤ (b:ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hE : 0 ≤ primeExponential g k b := (zero_le_one.trans (primeExponential_one_le g hg0 k b))
  have hC : 0 ≤ intervalConstant k := intervalConstant_nonneg k
  have hM : 0 ≤ powerfulMoment k := powerfulMoment_nonneg k
  rw [mul_comm (powerfulFunction k), convolution_sum_interval]
  let S := Finset.Icc 1 b
  let A := S.filter (· ≤ T)
  let D := S.filter (fun d => ¬d ≤ T)
  let W := fun d : ℕ => powerfulFunction k d *
    ∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e
  have hsplit : (∑ d ∈ S, W d) = (∑ d ∈ A, W d) + ∑ d ∈ D, W d :=
    (Finset.sum_filter_add_sum_filter_not S (fun d => d ≤ T) W).symm
  change (∑ d ∈ S, W d) ≤ _
  rw [hsplit]
  apply _root_.add_le_add
  · calc
      (∑ d ∈ A, W d) ≤ ∑ d ∈ A, (8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b) *
          (powerfulCorrection k d / (d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hds, hdT⟩ := Finset.mem_filter.mp hd
        have hd0 : 0 < d := (Finset.mem_Icc.mp hds).1
        obtain ⟨hTu, had, hrelative, _, hlogu, hlength⟩ :=
          divided_interval_estimates a b d T η hab hd0 hdT hT hTb hbT hη hηT hrel
        have hbase := hB g hg (a/d) (b/d) (hBT.trans hTu) had hrelative
        change (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) ≤
          intervalConstant k * ((((b/d:ℕ):ℝ)-(a/d:ℕ))/Real.log (b/d:ℕ)) * primeExponential g k (b/d) at hbase
        have hbound : (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) ≤
            intervalConstant k * (8*(((b:ℝ)-a)/Real.log b)/d) * primeExponential g k b := by
          apply hbase.trans
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hlength hC
          · exact primeExponential_mono g hg0 k (Nat.div_le_self b d)
          · exact Real.exp_nonneg _
          · positivity
        have hmul := mul_le_mul_of_nonneg_left hbound (powerfulCorrection_nonneg k d)
        calc
          W d = powerfulCorrection k d * (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) := rfl
          _ ≤ powerfulCorrection k d * (intervalConstant k * (8*(((b:ℝ)-a)/Real.log b)/d) * primeExponential g k b) := hmul
          _ = _ := by ring
      _ = (8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b) *
          ∑ d ∈ A, powerfulCorrection k d / (d:ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        have H := mul_le_mul_of_nonneg_left (powerfulCorrection_reciprocal_sum_le k A)
          (show 0 ≤ 8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b by positivity)
        convert H using 1
        ring
  · calc
      (∑ d ∈ D, W d) ≤ ∑ d ∈ D, ((b:ℝ)*(1+Real.log b)^k) * (powerfulCorrection k d/(d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have H := mul_le_mul_of_nonneg_left (primePenalty_pow_interval_trivial g hg k a b d hd0)
          (powerfulCorrection_nonneg k d)
        calc
          W d = powerfulCorrection k d * (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) := rfl
          _ ≤ powerfulCorrection k d * (((b:ℝ)/d) * (1+Real.log b)^k) := H
          _ = _ := by ring
      _ = ((b:ℝ)*(1+Real.log b)^k) * ∑ d ∈ D, powerfulCorrection k d/(d:ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        have H := powerfulCorrection_reciprocal_tail k D (T:ℝ) hT0 (by
          intro d hd
          have hdT := (Finset.mem_filter.mp hd).2
          exact_mod_cast (show T ≤ d by omega))
        have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ (b:ℝ)*(1+Real.log b)^k by positivity)
        convert H' using 1
        ring

end PrimeDegreePackets.Sieve

open Filter Topology
namespace PrimeDegreePackets.Sieve

lemma log_power_error_vanishes (k : ℕ) :
    Tendsto (fun b : ℕ => (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16))
      atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop ((k+1:ℕ):ℝ)
    (by norm_num : (0:ℝ) < 1/16)).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at H
  have H' : Tendsto (fun b : ℕ => (2:ℝ)^k * ((Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16)))
      atTop (𝓝 ((2:ℝ)^k * 0)) := tendsto_const_nhds.mul (H.comp tendsto_natCast_atTop_atTop)
  simpa only [mul_div_assoc, mul_zero] using H'

lemma eventual_tail_threshold (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ b : ℕ, B ≤ b → 1 ≤ Real.log b ∧
      (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η := by
  have H : ∀ᶠ b : ℕ in atTop, 1 ≤ Real.log b ∧
      (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η := by
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1:ℝ)), (log_power_error_vanishes k).eventually_le_const hη] with b hlog herr
    exact ⟨hlog, herr⟩
  exact eventually_atTop.mp H

lemma reciprocal_cutoff_bound (b T : ℕ) (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T^4) :
    (T:ℝ)^(-(1:ℝ)/4) ≤ (b:ℝ)^(-(1:ℝ)/16) := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  have H := Real.rpow_le_rpow_of_nonpos hb0 (show (b:ℝ) ≤ (T:ℝ)^4 by exact_mod_cast hbT)
    (by norm_num : -(1:ℝ)/16 ≤ 0)
  rw [← Real.rpow_natCast_mul hT0.le] at H
  norm_num at H ⊢
  exact H

lemma tail_absorbed (k a b T : ℕ) (η : ℝ) (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ T^4) (hlog : 1 ≤ Real.log b)
    (herr : (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η)
    (hrel : η*b ≤ (b:ℝ)-a) :
    ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) ≤ ((b:ℝ)-a)/Real.log b := by
  have hlog0 : 0 < Real.log b := by linarith
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  have hcut : (Real.log b * (1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) ≤ η := by
    calc
      _ ≤ (Real.log b * (2*Real.log b)^k) * (b:ℝ)^(-(1:ℝ)/16) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ hlog0.le
          exact pow_le_pow_left₀ (by linarith) (by linarith) k
        · exact reciprocal_cutoff_bound b T hb hT hbT
        · apply Real.rpow_nonneg; positivity
        · positivity
      _ = (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) := by
        rw [mul_pow, pow_succ, show -(1:ℝ)/16 = -((1:ℝ)/16) by ring, Real.rpow_neg hb0.le]
        ring
      _ ≤ η := herr
  apply (le_div_iff₀ hlog0).mpr
  have H := mul_le_mul_of_nonneg_left hcut hb0.le
  nlinarith only [H, hrel]

lemma sqrt_fourth_bound {b : ℕ} (hb : 4 ≤ b) : b ≤ (Nat.sqrt b)^4 := by
  have hs : 2 ≤ Nat.sqrt b := Nat.le_sqrt'.mpr hb
  have htop := Nat.lt_succ_sqrt' b
  have h1 : Nat.sqrt b + 1 ≤ (Nat.sqrt b)^2 := by nlinarith
  calc
    b ≤ (Nat.sqrt b + 1)^2 := by linarith
    _ ≤ ((Nat.sqrt b)^2)^2 := Nat.pow_le_pow_left h1 2
    _ = (Nat.sqrt b)^4 := by ring

end PrimeDegreePackets.Sieve
end
end

end OAI
