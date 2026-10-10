import OAI.NumberTheory.TotientAsymptotic.BootstrapExceptionalCount
import OAI.NumberTheory.TotientAsymptotic.CoordinateRealEndpoint
import OAI.NumberTheory.TotientAsymptotic.BootstrapLargeHead

namespace OAI

/-! Transfer the explicit preliminary exception to every real endpoint. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_good_real_gaussian : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧ ¬BootstrapGood ⌊x⌋₊ v) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  obtain ⟨A,hA,hcount⟩ := bootstrap_good_nat_count
  refine ⟨2*Real.exp 1*A,by positivity,?_⟩
  filter_upwards [tendsto_nat_floor_atTop.eventually hcount,
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (4:ℝ),
    bootstrap_error_gaussian_budget (by norm_num : (0:ℝ)<1/600000000),
    central_volume_one_le] with x hc hb hx hbudget hG
  intro Ψ hΨ Q hQ
  have hf := coordinate_floor_bounds hx
  have hbf : 0 ≤ B (⌊x⌋₊:ℝ) := by linarith only [hf.2.2.2.2.1,hb]
  have hbx : 0 ≤ B x := by linarith only [hb]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hlogf : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < ⌊x⌋₊ from lt_of_lt_of_le (by norm_num) hf.1))
  have hh := hc Q (by
    intro v hv
    exact ⟨(hQ v hv).1,Nat.le_floor (hQ v hv).2.1,(hQ v hv).2.2⟩)
  have hpoly : (B (⌊x⌋₊:ℝ)+4)^6*Real.exp (9*(Real.log (B (⌊x⌋₊:ℝ)+4))^2) ≤
      (B x+4)^6*Real.exp (9*(Real.log (B x+4))^2) := by
    have hlower : 0 ≤ Real.log (B (⌊x⌋₊:ℝ)+4) := Real.log_nonneg (by linarith only [hbf])
    have hl := Real.log_le_log (by linarith only [hbf] : 0 < B (⌊x⌋₊:ℝ)+4)
      (by linarith only [hf.2.2.2.2.2] : B (⌊x⌋₊:ℝ)+4 ≤ B x+4)
    apply mul_le_mul
    · exact pow_le_pow_left₀ (by linarith only [hbf]) (by linarith only [hf.2.2.2.2.2]) 6
    · apply Real.exp_le_exp.mpr
      nlinarith only [hlower,hl]
    · positivity
    · positivity
  have hnorm := coordinate_floor_normalization (δ:=1/600000000) hx (by norm_num) (by norm_num)
  have hweight : bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)) ≤
      2*Real.exp 1*bootstrapErrorWeight (B x)*(x/Real.log x) := by
    have hfac : 0 ≤ ((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ))*Real.exp (-(1/600000000:ℝ)*B (⌊x⌋₊:ℝ)) := by positivity
    have hprod := mul_le_mul hpoly hnorm hfac (by positivity)
    have he (b : ℝ) : Real.exp (9*(Real.log (b+4))^2-b/600000000)=
        Real.exp (9*(Real.log (b+4))^2)*Real.exp (-(1/600000000:ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold bootstrapErrorWeight
    rw [he,he]
    convert hprod using 1 <;> ring_nf
  have hsq : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have ht : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [ht,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hsave : bootstrapErrorWeight (B x) ≤ Real.exp (-(Ψ:ℝ)^2/4) := by
    have hh : bootstrapErrorWeight (B x) ≤ Real.exp (-(m x:ℝ)^2/4) := by
      simpa only [bootstrapErrorWeight,div_eq_mul_inv,one_mul,mul_comm] using hbudget
    exact hh.trans (Real.exp_le_exp.mpr (by linarith only [hsq]))
  have hbase : 0 ≤ (2*Real.exp 1*A)*(x/Real.log x) := by positivity
  calc
    _ ≤ A*bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)) := hh
    _ = A*(bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ))) := by ring
    _ ≤ A*(2*Real.exp 1*bootstrapErrorWeight (B x)*(x/Real.log x)) := mul_le_mul_of_nonneg_left hweight hA.le
    _ = ((2*Real.exp 1*A)*(x/Real.log x))*bootstrapErrorWeight (B x) := by ring
    _ ≤ ((2*Real.exp 1*A)*(x/Real.log x))*Real.exp (-(Ψ:ℝ)^2/4) := mul_le_mul_of_nonneg_left hsave hbase
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left hG hbase
      simpa only [mul_one] using mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le

lemma bootstrap_floor_good_large_head : ∀ᶠ x : ℝ in atTop,∀ v n : ℕ,
    BootstrapGood ⌊x⌋₊ v → x^(3/4:ℝ) < (v:ℝ) → 0 < n → n.totient=v →
    x^(1/4:ℝ) ≤ fordPrime n 0 := by
  filter_upwards [bootstrap_cofactor_size,bootstrap_residual_quarter,
    eventually_ge_atTop (4:ℝ)] with x hcof hquarter hx
  intro v n hv hlarge hn hφ
  have hmono := (coordinate_floor_bounds hx).2.2.2.2.2
  have hΩ : (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x := by
    rw [hφ]
    exact hv.1.1.trans (by linarith only [hmono])
  have hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x :=
    (hv.2 n hn hφ).trans (by linarith only [hmono])
  have htail := (hcof n hn hΩ hscore).trans hquarter
  apply quarter_prime_of_residual (by linarith only [hx]) hn htail
  simpa only [hφ] using hlarge

end TotientAsymptotic

end

end OAI
