import Mathlib
import OAI.Analysis.CoulombIonization.Variational.MasterRecovery
import OAI.Analysis.CoulombIonization.Variational.WidthKernelAmplitude
import OAI.Analysis.CoulombIonization.RadialBounds.RootMomentCauchyBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseKernelMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma masterCenteredKernel_ball_mass {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s R : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space)
    (hR : 2*masterWidth c₁ r₀ s y < R) :
    (∫ x, masterCenteredKernel c₁ r₀ s g y x ∂ballMeasure R) =
      ∫ x, masterKernel c₁ r₀ s g x y := by
  have hsup := masterCenteredKernel_support hg hgs hc hcL hr hs hs1 y
  change (∫ x in ball 0 R, masterCenteredKernel c₁ r₀ s g y x) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact integral_add_left_eq_self (fun x => masterKernel c₁ r₀ s g x y) y
  · by_contra hne
    have hh := hsup hne
    exact hx (mem_ball.mpr ((mem_closedBall.mp hh).trans_lt hR))

theorem masterCenteredKernel_mass_tendsto {ι : Type*} {l : Filter ι}
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    {r₀ s R : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, 2*masterWidth c₁ (r₀ i) (s i) (y i) < R i) :
    Tendsto (fun i => ∫ x, masterCenteredKernel c₁ (r₀ i) (s i) g (y i) x
      ∂ballMeasure (R i)) l (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := masterKernel_approximate_mass hg hgs hgn
  have hzero : Tendsto (fun i => C*c₁*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (C*c₁)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hzero
  filter_upwards [hr,hs,hR,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hri hsi hRi hs1
  rw [masterCenteredKernel_ball_mass hg hgs hc hcL hri hsi hs1.le _ hRi]
  exact hbound c₁ (r₀ i) (s i) hc hcL hri hsi hs1.le (y i)

theorem masterWidth_local_relative_tendsto {ι : Type*} {l : Filter ι}
    {c₁ : ℝ} (hc : 0 < c₁) {r₀ s : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0)) (hry : ∀ᶠ i in l, r₀ i ≤ ‖y i‖) :
    Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i))
      l (𝓝 0) := by
  have ht : Tendsto (fun i => (c₁*100000)*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (c₁*100000)
  apply squeeze_zero' _ _ ht
  · filter_upwards [hr,hs,hry] with i hri hsi hryi
    exact div_nonneg (masterWidth_pos hc hri hsi _).le (by unfold localCellRadius; positivity)
  · filter_upwards [hr,hs,hry] with i hri hsi hryi
    have hyi : y i ≠ 0 := norm_pos_iff.mp (hri.trans_le hryi)
    have ha := localCellRadius_pos hyi
    apply (div_le_iff₀ ha).mpr
    have hh := masterWidth_upper hc.le hri hsi (y i)
    rw [masterBaseDistance,max_eq_left hryi] at hh
    calc
      _ ≤ c₁*‖y i‖*(s i)^masterExponent := hh
      _ = _ := by unfold localCellRadius; ring

end Work_InverseKernelMass_barrier_scope

open Filter
open scoped Topology

open CoulombAnalysis

lemma rpow_inv_pow_bound {a t c e w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (ht : c*a^w ≤ t) (n : ℕ) :
    a^e*t⁻¹^n ≤ c⁻¹^n*a^(e-w*n) := by
  have hct : 0 < c*a^w := mul_pos hc (Real.rpow_pos_of_pos ha _)
  have hi := pow_le_pow_left₀ (inv_nonneg.mpr ((hct.trans_le ht).le))
    (inv_anti₀ hct ht) n
  have he : (c*a^w)⁻¹^n = c⁻¹^n*a^(-w*n) := by
    rw [mul_inv,mul_pow,←Real.rpow_neg ha.le,←Real.rpow_natCast (a^(-w)),←Real.rpow_mul ha.le]
  calc
    _ ≤ a^e*(c*a^w)⁻¹^n := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg ha.le _)
    _ = c⁻¹^n*(a^e*a^(-w*n)) := by rw [he]; ring
    _ = _ := by rw [←Real.rpow_add ha]; congr 2; ring

lemma inverse_duality_rescale {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (n L : ℝ) :
    (a^6)^2*((16*(n*t)^3*(L*t⁻¹^4)^2)*a^(-7+(1/100:ℝ))) =
      (16*n^3*L^2)*(a^(5+(1/100:ℝ))*t⁻¹^5) := by
  have he : a^12*a^(-7+(1/100:ℝ)) = a^(5+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  have he' : t^3*(t⁻¹^4)^2 = t⁻¹^5 := by
    field_simp
  calc
    _ = (16*n^3*L^2)*((a^12*a^(-7+(1/100:ℝ)))*(t^3*(t⁻¹^4)^2)) := by ring
    _ = _ := by rw [he,he']

lemma inverse_retained_rescale {a t A : ℝ} (ha : 0 < a) :
    a^6*(A*t⁻¹^3*a^(-3+(1/100:ℝ))) =
      A*(a^(3+(1/100:ℝ))*t⁻¹^3) := by
  have he : a^6*a^(-3+(1/100:ℝ)) = a^(3+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  calc
    _ = A*((a^6*a^(-3+(1/100:ℝ)))*t⁻¹^3) := by ring
    _ = _ := by rw [he]

theorem inverse_duality_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c n L : ℝ} (hc : 0 < c) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*Real.sqrt ((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (5+(1/100:ℝ))-(1+masterExponent)*5 := by norm_num [masterExponent]
  have hpow := ha0.rpow_const_nhds_zero he
  have hbound : Tendsto (fun i => (16*n^3*L^2*c⁻¹^5)*
      (a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) l (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (16*n^3*L^2*c⁻¹^5)
  have hscaled : Tendsto (fun i => ((a i)^6)^2*((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      positivity
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      rw [inverse_duality_rescale hai hti']
      calc
        _ ≤ (16*n^3*L^2)*(c⁻¹^5*(a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) :=
          mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 5) (by positivity)
        _ = _ := by ring
  have hh := hscaled.sqrt
  rw [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [ha,ht] with i hai hti
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_nonneg hai.le _)]

theorem inverse_retained_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*(A*(t i)⁻¹^3*(a i)^(-3+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (3+(1/100:ℝ))-(1+masterExponent)*3 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => (A*c⁻¹^3)*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3))
      l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero he).const_mul (A*c⁻¹^3)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht] with i hai hti
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    positivity
  · filter_upwards [ha,ht] with i hai hti
    rw [inverse_retained_rescale hai]
    calc
      _ ≤ A*(c⁻¹^3*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3)) :=
        mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 3) hA
      _ = _ := by ring

end CoulombAtom

end

end OAI
