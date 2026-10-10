import OAI.NumberTheory.JointDickman.Arithmetic.RoughPhaseEstimate
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveBudget

namespace OAI

/-! # The logarithmic cutoff for the remaining middle-frequency range -/
namespace JointDickman
open Filter Finset
open scoped Topology

lemma rough_logarithmic_cutoff : ∀ᶠ x : ℝ in atTop,
    1 < x ∧ 1 ≤ Real.log x ∧
    1 ≤ x/(Real.log x)^10 ∧ x/(Real.log x)^10 ≤ x ∧
    Real.log (x/(x/(Real.log x)^10)) = 10*Real.log (Real.log x) := by
  have hsmall := (log_power_div_power_tendsto_zero 10 (by norm_num : (0:ℝ)<1)).eventually
    (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hx hx1 hl
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hp : (Real.log x)^10 ≤ x := by
    simp only [Real.rpow_one,Real.rpow_ofNat] at hx
    exact (div_le_one hx0).mp hx
  refine ⟨hx1,hl,(le_div_iff₀ (pow_pos hl0 10)).mpr (by simpa using hp),?_,?_⟩
  · exact div_le_self hx0.le (one_le_pow₀ hl)
  · have he : x/(x/(Real.log x)^10) = (Real.log x)^10 := by field_simp
    rw [he,Real.log_pow]
    norm_num

lemma rough_cutoff_phase_loss {x t : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (ht : |t| ≤ 4*(Real.log x)^8) :
    (1+|t|)*(x/(Real.log x)^10)/x ≤ 5/(Real.log x)^2 := by
  have hl0 : 0 < Real.log x := by linarith
  have h8 : 1 ≤ (Real.log x)^8 := one_le_pow₀ hl
  have hnum : 1+|t| ≤ 5*(Real.log x)^8 := by linarith
  calc
    _ = (1+|t|)/(Real.log x)^10 := by field_simp
    _ ≤ (5*(Real.log x)^8)/(Real.log x)^10 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

lemma rough_prime_mass_bounded {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ x^c < (p:ℝ) ∧ (p:ℝ) ≤ x) →
      (∑ p ∈ P, 1/(p:ℝ)) ≤ -Real.log c+1 := by
  have hh := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [hh] with x hx P hP
  apply le_trans (b := ∑ p ∈ largePrimeSet x (x^c), 1/(p:ℝ))
  · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    intro p hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨Nat.le_floor (hP p hp).2.2,(hP p hp).1⟩,(hP p hp).2.1⟩
  · exact hx

lemma rough_phase_budget_tendsto (c M C : ℝ) (hc : 0 < c) (J : ℕ) :
    Tendsto (fun x : ℝ =>
      (2*(Real.log x)^(-(1:ℝ)/16)+45/(Real.log x)^2)*Real.exp (2*M)+
      2^J*((10*Real.log (Real.log x)+C)/(c*Real.log x))*(∑ h ∈ range J, M^h)+
      2/(⌊x^c⌋₊:ℝ)) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop
  have hn : Tendsto (fun x : ℝ => x^(-(1/16:ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hnear : Tendsto (fun x : ℝ => (Real.log x)^(-(1:ℝ)/16)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using hn.comp hlog
  have hpow : Tendsto (fun x : ℝ => (Real.log x)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hlog
  have hinv : Tendsto (fun x : ℝ => 45/(Real.log x)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)/Real.log x) atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1)).comp hlog
    simpa only [Function.comp_def,Real.rpow_one] using hh
  have hconst : Tendsto (fun x : ℝ => C/Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hratio : Tendsto (fun x : ℝ => (10*Real.log (Real.log x)+C)/(c*Real.log x))
      atTop (𝓝 0) := by
    have hh := ((hloglog.const_mul 10).add hconst).div_const c
    simpa only [mul_zero,add_zero,zero_div] using hh.congr (fun x => by ring)
  have hfloor : Tendsto (fun x : ℝ => (⌊x^c⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hc))
  have hlast : Tendsto (fun x : ℝ => 2/(⌊x^c⌋₊:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hfloor
  simpa only [mul_zero,add_zero,zero_mul] using
    ((((hnear.const_mul 2).add hinv).mul_const (Real.exp (2*M))).add
      ((hratio.const_mul (2^J)).mul_const (∑ h ∈ range J, M^h))).add hlast

end JointDickman

end OAI
