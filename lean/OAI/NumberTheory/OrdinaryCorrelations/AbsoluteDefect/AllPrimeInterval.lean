import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogCoef

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

namespace OrdinaryPrimeSupply
open Finset

lemma all_prime_interval (P Q : ℕ) (hPQ : P≤Q) :
    (∑p∈(Finset.Ioc P Q).filter Nat.Prime,(p:ℝ)⁻¹)=
      primeMass (0:ZMod 1) (Q:ℝ)-primeMass (0:ZMod 1) (P:ℝ) := by
  have he (n : ℕ) : (n:ZMod 1)=0 := Subsingleton.elim _ _
  simp only [primeMass,Nat.floor_natCast,he,and_true,sum_filter]
  have hei : Finset.Ioc P Q = Finset.Ico (P+1) (Q+1) := by
    ext n; simp only [Finset.mem_Ioc,Finset.mem_Ico]; omega
  simpa only [hei] using
    (sum_Ico_eq_sub (fun p : ℕ => if p.Prime then (p:ℝ)⁻¹ else 0) (by omega : P+1≤Q+1))

lemma loglog_two_pow_ratio {a b m : ℕ} (ha : 0<a) (he : b=a*2^m) :
    Real.log (Real.log ((2:ℝ)^b))-Real.log (Real.log ((2:ℝ)^a))=(m:ℝ)*Real.log 2 := by
  have ha' : (a:ℝ)≠0 := by exact_mod_cast ha.ne'
  have hb : (b:ℝ)≠0 := by rw [he]; positivity
  have hlog : Real.log 2≠0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  rw [Real.log_pow,Real.log_pow,Real.log_mul hb hlog,Real.log_mul ha' hlog]
  have hb' : (b:ℝ)=(a:ℝ)*(2:ℝ)^m := by exact_mod_cast he
  rw [hb',Real.log_mul ha' (by positivity),Real.log_pow]
  ring

lemma exp_one_le_two_pow {a : ℕ} (ha : 2≤a) : Real.exp 1≤(2:ℝ)^a := by
  have hl : (1:ℝ)/2≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have har : (2:ℝ)≤a := by exact_mod_cast ha
  have hh : 1≤(a:ℝ)*Real.log 2 := by nlinarith only [hl,har]
  have he := Real.exp_le_exp.mpr hh
  simpa only [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] using he

theorem dyadic_prime_mass_bound :
    ∃C : ℝ,0≤C ∧ ∀a m : ℕ,2≤a →
      |(∑p∈(Finset.Ioc (2^a) (2^(a*2^m))).filter Nat.Prime,(p:ℝ)⁻¹)-(m:ℝ)*Real.log 2|≤C := by
  obtain ⟨C,hC,hbound⟩ := primeMass_loglog_bound (0:ZMod 1) (by rw [Subsingleton.elim (0:ZMod 1) 1]; exact isUnit_one)
  refine ⟨2*C,by positivity,?_⟩
  intro a m ha
  have hab : a≤a*2^m := Nat.le_mul_of_pos_right _ (by positivity)
  have hP := hbound ((2:ℝ)^a) (exp_one_le_two_pow ha)
  have hQ := hbound ((2:ℝ)^(a*2^m)) (exp_one_le_two_pow (ha.trans hab))
  norm_num only [Nat.totient_one,Nat.cast_one,inv_one,one_mul] at hP hQ
  rw [all_prime_interval (2^a) (2^(a*2^m)) (Nat.pow_le_pow_right (by omega) hab)]
  push_cast
  rw [←loglog_two_pow_ratio (by omega : 0<a) (rfl : a*2^m=a*2^m)]
  have hh := abs_sub_le (primeMass (0:ZMod 1) ((2:ℝ)^(a*2^m))-Real.log (Real.log ((2:ℝ)^(a*2^m))))
    (0:ℝ) (primeMass (0:ZMod 1) ((2:ℝ)^a)-Real.log (Real.log ((2:ℝ)^a)))
  simp only [sub_zero,zero_sub,abs_neg] at hh
  have he : primeMass (0:ZMod 1) ((2:ℝ)^(a*2^m))-primeMass (0:ZMod 1) ((2:ℝ)^a)-
      (Real.log (Real.log ((2:ℝ)^(a*2^m)))-Real.log (Real.log ((2:ℝ)^a)))=
      (primeMass (0:ZMod 1) ((2:ℝ)^(a*2^m))-Real.log (Real.log ((2:ℝ)^(a*2^m))))-
      (primeMass (0:ZMod 1) ((2:ℝ)^a)-Real.log (Real.log ((2:ℝ)^a))) := by ring
  rw [he]
  linarith

end OrdinaryPrimeSupply

end

end OAI
