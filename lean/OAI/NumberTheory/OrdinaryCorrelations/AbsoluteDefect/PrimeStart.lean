import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeLogReciprocalBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AllPrimeInterval

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryUniformWidth
open OrdinaryCorrelations OrdinaryNarrowGrid OrdinaryPrimeSupply Finset Filter

def primeStart (m : ℕ) : ℕ := 8*m+2
def primeSpan (v m : ℕ) : ℕ := primeStart m*2^(2*m+v)-primeStart m

def accuracy (m : ℕ) : ℝ := (1/2:ℝ)^(2*m)

lemma accuracy_pos (m : ℕ) : 0<accuracy m := by unfold accuracy;positivity

lemma prime_extent (v m : ℕ) : primeStart m+primeSpan v m=primeStart m*2^(2*m+v) := by
  unfold primeSpan
  exact Nat.add_sub_of_le (Nat.le_mul_of_pos_right _ (by positivity))

lemma prime_span_le (v m : ℕ) : primeSpan v m≤primeStart m*2^(2*m+v) := Nat.sub_le _ _

lemma choose_prime_packet : ∃v : ℕ, ∀m : ℕ,
    1≤∑p∈primeWindow 1 (primeStart m) (primeSpan v m),(p:ℝ)⁻¹ ∧
    Real.exp (-(∑p∈primeWindow 1 (primeStart m) (primeSpan v m),(p:ℝ)⁻¹))≤accuracy m := by
  obtain ⟨C,hC,hM⟩ := dyadic_prime_mass_bound
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨v,hv⟩ := exists_nat_ge ((C+1)/Real.log 2)
  have hv' : C+1≤(v:ℝ)*Real.log 2 := (div_le_iff₀ hl).mp hv
  refine ⟨v,?_⟩
  intro m
  have hm := hM (primeStart m) (2*m+v) (by unfold primeStart;omega)
  have he : primeWindow 1 (primeStart m) (primeSpan v m)=
      (Finset.Ioc (2^primeStart m) (2^(primeStart m*2^(2*m+v)))).filter Nat.Prime := by
    simp only [primeWindow,one_mul,prime_extent]
  rw [←he] at hm
  have hlow := (abs_le.mp hm).1
  push_cast at hlow
  have hstrong : (2*(m:ℝ))*Real.log 2+1≤∑p∈primeWindow 1 (primeStart m) (primeSpan v m),(p:ℝ)⁻¹ := by
    nlinarith only [hlow,hv']
  refine ⟨by nlinarith only [hstrong,mul_nonneg (by positivity : 0≤2*(m:ℝ)) hl.le],?_⟩
  have hexp := Real.exp_le_exp.mpr (by linarith only [hstrong] :
    -(∑p∈primeWindow 1 (primeStart m) (primeSpan v m),(p:ℝ)⁻¹) ≤ -(2*(m:ℝ))*Real.log 2)
  have hid : Real.exp (-(2*(m:ℝ))*Real.log 2)=accuracy m := by
    rw [neg_mul,Real.exp_neg]
    have hn : 2*(m:ℝ)=((2*m:ℕ):ℝ) := by push_cast;ring
    rw [hn,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp [accuracy,inv_pow]
  exact hexp.trans_eq hid

lemma diagonal_small (m : ℕ) : (3/4:ℝ)^primeStart m≤accuracy m := by
  unfold primeStart accuracy
  rw [pow_add,pow_mul]
  calc
    _ ≤ (1/4:ℝ)^m*1 := by gcongr <;> norm_num
    _ = _ := by rw [pow_mul];norm_num

lemma square_small (m : ℕ) : 2/(2:ℝ)^primeStart m≤2*accuracy m := by
  have he : (2:ℝ)⁻¹=1/2 := by norm_num
  rw [div_eq_mul_inv,←inv_pow,he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold primeStart;omega)

lemma resonance_small (v : ℕ) : ∀ᶠ m : ℕ in atTop,
    (primeSpan v m:ℝ)*Real.sqrt (4/((2^(10*m):ℕ):ℝ))≤accuracy m := by
  have ht1 := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have ht2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have ht : Tendsto (fun m : ℕ=>2*(2:ℝ)^v*(8*(m:ℝ)+2)*(1/2:ℝ)^m) atTop (nhds 0) := by
    have hh := (ht1.const_mul (16*(2:ℝ)^v)).add (ht2.const_mul (4*(2:ℝ)^v))
    simpa only [mul_zero,add_zero] using (hh.congr' (Filter.Eventually.of_forall (fun m=>by ring)))
  filter_upwards [(tendsto_order.mp ht).2 1 (by norm_num)] with m hm
  have he : Real.sqrt (4/((2^(10*m):ℕ):ℝ))=2*(1/2:ℝ)^(5*m) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    symm
    push_cast
    rw [mul_pow,pow_two (2:ℝ)]
    have hp : ((1/2:ℝ)^(5*m))^2=(1/2:ℝ)^(10*m) := by rw [←pow_mul];congr 1;omega
    rw [hp]
    norm_num [div_eq_mul_inv,inv_pow]
    rw [one_div,inv_pow]
  rw [he]
  have hr : (primeSpan v m:ℝ)≤(8*(m:ℝ)+2)*(2:ℝ)^(2*m+v) := by
    have hh := prime_span_le v m
    exact_mod_cast hh
  calc
    _ ≤ ((8*(m:ℝ)+2)*(2:ℝ)^(2*m+v))*(2*(1/2:ℝ)^(5*m)) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = (2*(2:ℝ)^v*(8*(m:ℝ)+2)*(1/2:ℝ)^m)*accuracy m := by
      have hp : (2:ℝ)^(2*m)*(1/2:ℝ)^(2*m)=1 := by rw [←mul_pow];norm_num
      rw [pow_add,show 5*m=2*m+(m+2*m) by omega,pow_add,pow_add]
      unfold accuracy
      calc
        _ = ((2:ℝ)^(2*m)*(1/2:ℝ)^(2*m))*(2*(2:ℝ)^v*(8*(m:ℝ)+2)*(1/2:ℝ)^m*(1/2:ℝ)^(2*m)) := by ring
        _ = _ := by rw [hp,one_mul]
    _ ≤ accuracy m := by nlinarith only [hm,(accuracy_pos m)]

end OrdinaryUniformWidth

end

end OAI
