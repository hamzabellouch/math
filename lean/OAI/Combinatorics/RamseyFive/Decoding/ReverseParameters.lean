import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

theorem eventually_reverse_parameters {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R b τ : ℝ), Range η σ D R →
      b≤Cb*D*σ^(6*beta η) → 0≤τ → τ≤σ^(-200*beta η) →
      1≤P η σ D R ∧ b≤P η σ D R ∧ 1000≤Real.exp (P η σ D R) ∧
      1000*τ≤(9:ℝ)/10 ∧ 3≤Real.exp σ := by
  have hh := eventually_hierarchy hη hη' Cb 1 1 hCb (by norm_num)
  have hc := eventually_power_absorption hη hη' 1000 0 1 (by norm_num) (by norm_num) (by norm_num)
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)<(9:ℝ)/10000 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const (by norm_num : (0:ℝ)<9/10000)
  filter_upwards [hh,hc,ht,eventually_ge_atTop (10:ℝ)] with σ hh hc ht hσ
  intro D R b τ hr hb hτ hτhi
  have hv := hh D R b τ hr hb hτhi
  have hP : 1≤P η σ D R := by linarith only [hv.1,hv.2.2.2.2.2]
  have hbP : b≤P η σ D R := by
    have hn : 0≤P η σ D R*τ := mul_nonneg (le_trans (by norm_num) hP) hτ
    linarith only [hv.2.2.2.2.1,hv.2.2.2.2.2,hn]
  refine ⟨hP,hbP,?_,?_,?_⟩
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc D R hr
  · linarith only [hτhi,ht]
  · linarith only [Real.add_one_le_exp σ,hσ]

end SharpRamseyFive.ParameterHierarchy

namespace SharpRamseyFive.ReverseCap
open scoped Classical

noncomputable def reverseLength (q gap : ℝ) : ℕ := ⌈20*q*(gap+1)⌉₊

lemma reverseLength_spec (q gap : ℝ) (hq : 1≤q) (hg : 0≤gap) :
    0<reverseLength q gap ∧ 20*q*gap≤reverseLength q gap ∧
    (reverseLength q gap:ℝ)≤21*q*(gap+1) := by
  have hq' : 0<q := by linarith
  have hp : 0<20*q*(gap+1) := by positivity
  have hl := Nat.le_ceil (20*q*(gap+1))
  have hu := Nat.ceil_lt_add_one hp.le
  refine ⟨Nat.ceil_pos.mpr hp,?_,?_⟩
  · dsimp [reverseLength]
    nlinarith only [hl,hq']
  · dsimp [reverseLength]
    have hh : 1≤q*(gap+1) := by nlinarith
    nlinarith only [hu,hh]

lemma reverse_cost_scalar (q P gap n : ℝ) (hq : 1≤q) (hP : 1≤P)
    (hg : 0≤gap) (hn : 0≤n) (hnhi : n≤21*q*(gap+1)) :
    Real.log (2*q)-Real.log ((9:ℝ)/10)+n*(2*P-Real.log ((9:ℝ)/10))≤
      100*q*P*(gap+P) := by
  have hq' : 0<q := by linarith
  have hln := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/10)
  norm_num at hln
  have hlq := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hc : 2*P-Real.log ((9:ℝ)/10)≤3*P := by linarith only [hln,hP]
  have hm := mul_le_mul_of_nonneg_left hc hn
  have hna := mul_le_mul_of_nonneg_right hnhi (by linarith : (0:ℝ)≤3*P)
  have hqp : q≤q*P := by nlinarith
  have hpp : q*P≤q*P*P := by nlinarith
  have hg' : 0≤q*P*gap := by positivity
  nlinarith only [hlq,hln,hm,hna,hqp,hpp,hg',hq]

end SharpRamseyFive.ReverseCap

end OAI
