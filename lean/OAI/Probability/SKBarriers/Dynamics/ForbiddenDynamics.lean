import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ClockEndpoint
import OAI.Probability.SKBarriers.Coverage.FiniteCoverageMixing
import OAI.Probability.SKBarriers.Dynamics.GreedyEventual

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem mixedMass_le_pairStrip {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    {a₀ a₁ q a δ L : ℝ} (ha₀ : 0<a₀) (haq : a₁<q) (ha : 0<a)
    (hgap : 2/(n:ℝ)<a₁-a₀) (hL : 0≤L) (htail : (n:ℝ)*Real.exp (-L)≤(1/8:ℝ))
    (hcov : (gibbsFiniteLaw β J).prob (fun x => (gibbsFiniteLaw β J).prob (fun y => q≤|overlap x y|)<a)≤δ) :
    continuousMixedMass β J (Real.exp L)≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) ∧
    discreteMixedMass β J ⌊Real.exp L⌋₊≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
  have hnum : (⌊Real.exp L⌋₊:ℝ)+1≤(⌈Real.exp (2*L)⌉₊:ℝ)+1 := by
    have H : ⌊Real.exp L⌋₊≤⌈Real.exp (2*L)⌉₊ :=
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hL]))).trans (Nat.floor_le_ceil _)
    exact_mod_cast Nat.add_le_add_right H 1
  have HC (v : Config n) :
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ continuousDistance β J x (Real.exp L)≤(1/4:ℝ))≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
    convert mass_continuous_mixed_high_le_strip hn β J v ha₀ hgap L htail using 1 <;> simp only [gibbs_prob_eq_sum,Nat.cast_add,Nat.cast_one]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
  have HD (v : Config n) :
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ discreteDistance β J x ⌊Real.exp L⌋₊≤(1/4:ℝ))≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
    have H := mass_mixed_high_le_strip hn β J v ha₀ hgap ⌊Real.exp L⌋₊
    have HH : (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ discreteDistance β J x ⌊Real.exp L⌋₊≤(1/4:ℝ))≤
        (4*((⌊Real.exp L⌋₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
      convert H using 1 <;> simp only [gibbs_prob_eq_sum,Nat.cast_add,Nat.cast_one]
      · apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
    refine HH.trans (mul_le_mul_of_nonneg_right ?_ ((gibbsFiniteLaw β J).prob_nonneg _))
    nlinarith only [hnum,(Nat.cast_nonneg (⌈Real.exp (2*L)⌉₊) : (0:ℝ)≤_)]
  have general (E : Config n → Prop)
      (HE : ∀v,(gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁)) :
      (gibbsFiniteLaw β J).prob E≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
    have H := covered_mixed_mass_le_signed_average β J E haq ha hcov
    have HB := (gibbsFiniteLaw β J).expect_mono HE
    rw [FiniteLaw.expect_const_mul,pairStrip_expect] at HB
    refine H.trans (add_le_add_right ((mul_le_mul_of_nonneg_left HB (by positivity : 0≤2/a)).trans_eq ?_) δ)
    ring
  constructor
  · simpa only [gibbs_prob_eq_sum,continuousMixedMass] using general _ HC
  · simpa only [gibbs_prob_eq_sum,discreteMixedMass] using general _ HD

 theorem pairStrip_numerical_error {L c v : ℝ} (hL : 0≤L) (hv : v≤Real.exp (-(c+10)*L)) :
    Real.exp (-3*L)+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L))*v≤
      Real.exp (-3*L)+48*Real.exp (-8*L) := by
  apply add_le_add_right
  have HM := horizon_size_bound hL
  have HN : 0≤16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L) := by positivity
  calc
    _ ≤ (16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L))*Real.exp (-(c+10)*L) := mul_le_mul_of_nonneg_left hv HN
    _ ≤ (16*(3*Real.exp (2*L))/Real.exp (-c*L))*Real.exp (-(c+10)*L) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left HM (by norm_num)) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc 16 3,show (16:ℝ)*3=48 by norm_num,mul_div_assoc,← Real.exp_sub,mul_assoc,← Real.exp_add]
      congr 2
      ring

end SK.Analytic

end
end

end OAI
