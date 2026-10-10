import Mathlib
import OAI.Analysis.CoulombIonization.Variational.MasterKernelFubini

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierTruncation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def innerPotential (r : ℝ) (ρ : Space → ℝ) (y : Space) : ℝ :=
  ∫ z in ball (0 : Space) r, ρ z/‖y-z‖

lemma innerPotential_eq_tfPotential (r : ℝ) (ρ : Space → ℝ) (y : Space) :
    innerPotential r ρ y = tfPotential ((ball (0 : Space) r).indicator ρ) y := by
  unfold innerPotential tfPotential
  rw [←integral_indicator measurableSet_ball]
  congr 1
  funext z
  by_cases hz : z ∈ ball (0 : Space) r <;> simp [hz]

lemma innerPotential_nonneg {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) (r : ℝ) (y : Space) :
    0 ≤ innerPotential r ρ y := integral_nonneg (fun z => div_nonneg (hn z) (norm_nonneg _))

lemma masterWidth_le_half_radius {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hc1 : c₁ ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) {x : Space} (hx : r₀ ≤ ‖x‖) :
    masterWidth c₁ r₀ s x ≤ ‖x‖/2 := by
  have hpow : s^masterExponent ≤ 1 := by
    simpa using Real.rpow_le_rpow hs.le hs1 masterExponent_nonneg
  have hb := masterWidth_upper hc hr hs x
  simp only [masterBaseDistance,max_eq_left hx] at hb
  calc
    _ ≤ c₁*‖x‖*s^masterExponent := hb
    _ ≤ c₁*‖x‖*1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ ‖x‖/2 := by nlinarith [norm_nonneg x]

lemma masterKernel_zero_inner {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1)
    {x z : Space} (hx : 2*r₀ ≤ ‖x‖) (hz : ‖z‖ < r₀) :
    masterKernel c₁ r₀ s g x z = 0 := by
  have hb := masterWidth_le_half_radius hc.le hc1 hr hs hs1 (by linarith : r₀ ≤ ‖x‖)
  have hnorm : ‖x‖ ≤ ‖z-x‖+‖z‖ := by
    simpa only [norm_sub_rev] using (norm_le_norm_sub_add x z)
  have he : scaledRealPacket (masterWidth c₁ r₀ s x) g (z-x) = 0 := by
    by_contra hn
    have hh := scaledRealPacket_support (masterWidth_pos hc hr hs x) hgs hn
    linarith
  simp only [masterKernel,he,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

lemma inner_master_potential_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (r : ℝ) (y : Space) :
    Measurable (fun x => innerPotential r (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma inner_master_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (r : ℝ) (x y : Space) :
    innerPotential r (masterKernel c₁ r₀ s g x) y ≤ tfPotential (masterKernel c₁ r₀ s g x) y := by
  exact setIntegral_le_integral (masterKernel_pole_integrable hc hr hs hg hcg x y)
    (ae_of_all _ (fun z => div_nonneg (masterKernel_nonneg c₁ r₀ s g x z) (norm_nonneg _)))

theorem inner_master_potential_raw_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hc1 : c₁ ≤ 1/2) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) (hy : ‖y‖ ≤ (11/10)*r₀) :
    innerPotential r₀ (masterKernel c₁ r₀ s g x) y ≤
      if ‖x-y‖ < 4*r₀ then 1/‖x-y‖ else 0 := by
  by_cases hx : ‖x‖ < 2*r₀
  · have hd : ‖x-y‖ < 4*r₀ := by
      have ht := norm_sub_le x y
      linarith
    rw [ite_eq_left hd]
    exact (inner_master_potential_le hc hr hs hg hcg r₀ x y).trans
      (by simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs hxy)
  · have he : innerPotential r₀ (masterKernel c₁ r₀ s g x) y = 0 := by
      unfold innerPotential
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      rw [masterKernel_zero_inner hc hc1 hr hs hs1 hgs (le_of_not_gt hx)
        (by simpa only [mem_ball,dist_zero_right] using hz),zero_div]
    rw [he]
    split_ifs <;> positivity

lemma inner_master_configuration_integrable {N : ℕ} (ν : Measure (Configuration N))
    (r : ℝ) (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (inner_master_potential_measurable hc hr hs hg.continuous r y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
    innerPotential_nonneg (masterKernel_nonneg c₁ r₀ s g (x i)) r y))]
  apply Finset.sum_le_sum
  intro i _
  exact (inner_master_potential_le hc hr hs hg hcg r (x i) y).trans
    (by simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i))

theorem inner_master_configuration_fubini {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (r : ℝ) (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    innerPotential r (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y =
      ∫ x, ∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y ∂ν := by
  have hp := (master_configuration_pole_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs).mono_measure
    (Measure.prod_mono (le_refl ν) (Measure.restrict_le_self (s := ball (0 : Space) r)))
  unfold innerPotential
  calc
    _ = ∫ z in ball (0 : Space) r, ∫ x, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖ ∂ν := by
      simp only [integral_div]
    _ = ∫ x, (∫ z in ball (0 : Space) r, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖) ∂ν :=
      integral_integral_swap hp.swap
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [Finset.sum_div]
        exact integral_finsetSum _ (fun i _ => (masterKernel_pole_integrable hc hr hs hg hcg (x i) y).integrableOn))

end CoulombAtom

end Work_BarrierTruncation_barrier_scope

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def DeterministicLocalBound {Ω : Type*} (u : Ω → TFSpace → ℝ) : Prop :=
  ∀ K : Set TFSpace, IsCompact K → ∃ C : ℝ, ∀ sample x, x ∈ K → ‖u sample x‖ ≤ C

end CoulombBarrier

end

end OAI
