import Mathlib
import OAI.Analysis.CoulombIonization.Variational.LocalWidthKernel

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma scaled_packet_density_radial (b : ℝ) {g : Space → ℝ} (hr : IsRadial g) :
    IsRadial (fun x => (scaledRealPacket b g x)^2) := by
  intro x y hxy
  dsimp only
  rw [scaledRealPacket_radial b hr x y hxy]

lemma scaled_packet_density_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) (x : Space) (hx : (scaledRealPacket b g x)^2 ≠ 0) :
    ‖x‖ ≤ b := (scaledRealPacket_support hb hs (by intro hz; exact hx (by rw [hz]; norm_num))).le

lemma scaled_packet_potential_le {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : x ≠ 0) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x ≤ 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    funext z
    exact pow_two _
  have hh := radial_potential_le_point (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (fun z => sq_nonneg _)
    (scaled_packet_density_radial b hr) hb.le (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma scaled_packet_potential_eq {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : b ≤ ‖x‖) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x = 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    funext z
    exact pow_two _
  have hh := tfPotential_newton_exterior_closed (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (scaled_packet_density_radial b hr) hb
    (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma masterKernel_potential_centered (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    tfPotential (masterKernel c₁ r₀ s g x) y =
      tfPotential (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) (y-x) :=
  integral_translated_pole (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) y x

lemma masterKernel_potential_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ tfPotential (masterKernel c₁ r₀ s g x) y :=
  tfPotential_nonneg (ae_of_all _ (masterKernel_nonneg c₁ r₀ s g x)) y

lemma masterKernel_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    tfPotential (masterKernel c₁ r₀ s g x) y ≤ 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_le (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (sub_ne_zero.mpr hxy.symm)

lemma masterWidth_le_distance {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) {x y : Space}
    (hxy : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖) :
    masterWidth c₁ r₀ s x ≤ ‖y-x‖ := by
  have hh := (masterWidth_small_lipschitz hc hcL hr hs hs1).dist_le_mul x y
  simp only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
  rw [norm_sub_rev x y] at hh
  have h := (le_abs_self (masterWidth c₁ r₀ s x-masterWidth c₁ r₀ s y)).trans hh
  linarith

lemma masterKernel_potential_eq_far {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖) :
    tfPotential (masterKernel c₁ r₀ s g x) y = 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_eq (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (masterWidth_le_distance hc hcL hr hs hs1 hxy)

theorem masterKernel_potential_loss {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    0 ≤ 1/‖y-x‖-tfPotential (masterKernel c₁ r₀ s g x) y ∧
      1/‖y-x‖-tfPotential (masterKernel c₁ r₀ s g x) y ≤
        (ball y (2*masterWidth c₁ r₀ s y)).indicator (fun x => 1/‖y-x‖) x := by
  refine ⟨sub_nonneg.mpr (masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs hxy),?_⟩
  by_cases hx : x ∈ ball y (2*masterWidth c₁ r₀ s y)
  · rw [indicator_of_mem hx]
    linarith [masterKernel_potential_nonneg c₁ r₀ s g x y]
  · rw [indicator_of_notMem hx]
    have hfar : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖ := by
      simpa only [mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hx
    rw [masterKernel_potential_eq_far hc hcL hr hs hs1 hg hcg hgn hrad hgs hfar,sub_self]

end CoulombAtom

end

end OAI
