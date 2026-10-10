import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs
import OAI.NumberTheory.TotientAsymptotic.SuffixSize

namespace OAI

/-! Uniform size of the actual suffix following a first differing prime. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collision_coarse_sizes : ∀ᶠ x : ℝ in atTop, ∀ H i : ℕ,
    1 ≤ i → i+2 ≤ L x H → L x H < m x → ∀ η : RemainderDatum (L x H),
    IsBasicRemainder x H η →
    (22/25 : ℝ)*fordBandScale x i ≤ B (remainderPrime η i) ∧
    B (remainderPrime η i) ≤ (28/25 : ℝ)*fordBandScale x i ∧
    Real.log (suffixPreimage η i : ℝ) ≤
      ((m x-i : ℕ)+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro H i hi hiL hL η hη
  have him : i < m x := by omega
  have hb := bandScale_pos him
  have hflo : (99/100 : ℝ)*bandScale x i < fordBandScale x i :=
    (lt_div_iff₀ hb).mp (by linarith [(abs_lt.mp (hx i him)).1])
  have hfhi : fordBandScale x i < (101/100 : ℝ)*bandScale x i :=
    (div_lt_iff₀ hb).mp (by linarith [(abs_lt.mp (hx i him)).2])
  have hp := hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)
  have hu : (9/10 : ℝ)*bandScale x i ≤ B (remainderPrime η i) ∧
      B (remainderPrime η i) ≤ (11/10 : ℝ)*bandScale x i := by
    simpa only [remainderCoord,B,ite_eq_right (by omega : i ≠ 0)] using hp.2
  refine ⟨by nlinarith,by nlinarith,?_⟩
  have hs1 : bandScale x (i+1) ≤ (137/250 : ℝ)*bandScale x i := by
    exact (bandScale_succ_le x i).trans
      (mul_le_mul_of_nonneg_right collision_rho_bounds.2.le hb.le)
  have hs2 : bandScale x (i+2) ≤ (137/250 : ℝ)^2*bandScale x i := by
    have h := (bandScale_succ_le x (i+1)).trans
      (mul_le_mul_of_nonneg_right collision_rho_bounds.2.le (bandScale_nonnegative x (i+1)))
    have h' := mul_le_mul_of_nonneg_left hs1 (by norm_num : (0 : ℝ) ≤ 137/250)
    convert h.trans h' using 1
    ring
  have hlast := (bandScale_antitone x hiL).trans hs2
  have hnext : (11/10 : ℝ)*bandScale x (i+1) ≤ (7/10 : ℝ)*fordBandScale x i := by
    nlinarith
  have hcof : 2*bandScale x (L x H) ≤ (7/10 : ℝ)*fordBandScale x i := by
    nlinarith
  have hcount : ((L x H-i : ℕ) : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast Nat.sub_le_sub_right hL.le i
  calc
    _ ≤ (L x H-i : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (i+1))+
        Real.exp (2*bandScale x (L x H)) := basic_suffix_log_bound hη
    _ ≤ (m x-i : ℕ)*Real.exp ((7/10 : ℝ)*fordBandScale x i)+
        Real.exp ((7/10 : ℝ)*fordBandScale x i) :=
      add_le_add (mul_le_mul hcount (Real.exp_le_exp.mpr hnext)
        (Real.exp_pos _).le (Nat.cast_nonneg _)) (Real.exp_le_exp.mpr hcof)
    _ = _ := by ring

lemma collision_tail_ratio_decay : ∀ᶠ b : ℝ in atTop,
    (b+1)*Real.exp ((7/10 : ℝ)*b) ≤ (1/1000 : ℝ)*Real.exp ((22/25 : ℝ)*b) := by
  have ht : Tendsto (fun b : ℝ => (b+1)*Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => b*Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) := by
      simpa only [Real.rpow_one] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (9/50) (by norm_num)
    have h0 : Tendsto (fun b : ℝ => Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
    simpa only [add_mul,one_mul,add_zero] using h1.add h0
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/1000))] with b hb
  have hh := mul_le_mul_of_nonneg_right hb.le (Real.exp_pos ((22/25 : ℝ)*b)).le
  have he : ((b+1)*Real.exp (-(9/50 : ℝ)*b))*Real.exp ((22/25 : ℝ)*b) =
      (b+1)*Real.exp ((7/10 : ℝ)*b) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rwa [he] at hh

/-- After any retained positive index, the whole residual preimage, including
its possibly repeated final prime, has logarithm at most one per mille of the
logarithm of the first prime. -/
theorem collision_tail_log_small : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    Real.log (suffixPreimage η i : ℝ) ≤ (1/1000 : ℝ)*Real.log (remainderPrime η i : ℝ) := by
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp collision_tail_ratio_decay
  filter_upwards [ford_band_polynomial_lower 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop b₀),
    eventually_ge_atTop 1] with H hpoly hH hH1
  filter_upwards [hpoly,collision_coarse_sizes] with x hx hcoarse
  intro i hi hiR hiL hL η hη
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hx i him hHi
  have hHiR : (H : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hHi
  have hB : b₀ ≤ fordBandScale x i := hH.trans (hHiR.trans hb)
  obtain ⟨hlo,_,htail⟩ := hcoarse H i hi hiL hL η hη
  have hp : (1 : ℝ) < remainderPrime η i := by
    exact_mod_cast (hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)).1.one_lt
  have hexp : Real.exp ((22/25 : ℝ)*fordBandScale x i) ≤ Real.log (remainderPrime η i : ℝ) := by
    have he := Real.exp_le_exp.mpr hlo
    simpa only [B,Real.exp_log (Real.log_pos hp)] using he
  calc
    _ ≤ ((m x-i : ℕ)+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) := htail
    _ ≤ (fordBandScale x i+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (1/1000 : ℝ)*Real.exp ((22/25 : ℝ)*fordBandScale x i) := hb₀ _ hB
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by norm_num)

end TotientAsymptotic

end

end OAI
