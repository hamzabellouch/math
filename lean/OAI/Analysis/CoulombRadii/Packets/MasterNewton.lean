import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel
import OAI.Analysis.CoulombRadii.Packets.PacketWidthScalar
import OAI.Analysis.CoulombRadii.Packets.PacketDensity
import OAI.Analysis.CoulombRadii.FieldAnalysis.MeridianMap

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma fixed_scaled_window_mass (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {t : ℝ} (ht : 0<t) : (∫ w : Position,(t^3)⁻¹*g (t⁻¹ • w)^2)=1 := by
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun w : Position => g w^2) ht.le]
  simp only [Position,finrank_euclideanSpace_fin,smul_eq_mul,hm,mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

lemma fixed_scaled_window_integrable (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {t : ℝ} (ht : 0<t) : Integrable (fun w : Position => (t^3)⁻¹*g (t⁻¹ • w)^2) := by
  by_contra hn
  have hh := integral_undef hn
  rw [fixed_scaled_window_mass g hm ht] at hh
  exact one_ne_zero hh

lemma packet_potential_center_shift (g : Position → ℝ) (c r₀ s : ℝ) (z y : Position) :
    potentialOf (packetKernel g c r₀ s z) y =
      ∫ w, Coulomb.coulombKernel ((y-z)-w)*
        ((packetWidth c r₀ s z^3)⁻¹*g ((packetWidth c r₀ s z)⁻¹ • w)^2) := by
  rw [←integral_sub_right_eq_self (fun w : Position => Coulomb.coulombKernel ((y-z)-w)*
    ((packetWidth c r₀ s z^3)⁻¹*g ((packetWidth c r₀ s z)⁻¹ • w)^2)) z]
  unfold potentialOf packetKernel
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [show (y-z)-(w-z)=y-w by abel]
    rfl

theorem packet_potential_newton (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    {z y : Position} (hyz : y≠z) :
    0≤potentialOf (packetKernel g c r₀ s z) y ∧
    potentialOf (packetKernel g c r₀ s z) y≤coulombKernel (y-z) := by
  let t := packetWidth c r₀ s z
  have ht : 0<t := packetWidth_pos hc hr hs z
  have hp (w : Position) : 0≤(t^3)⁻¹*g (t⁻¹ • w)^2 := by positivity
  have hb (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2≤(t^3)⁻¹*(SchwartzMap.seminorm ℝ 0 0 g)^2 :=
    mul_le_mul_of_nonneg_left (Coulomb.schwartz_square_le g _) (by positivity)
  have hfr (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2=
      (t^3)⁻¹*g (t⁻¹ • EuclideanSpace.single 0 ‖w‖)^2 := by
    have hh : ‖t⁻¹ • w‖=‖t⁻¹ • EuclideanSpace.single (0:Fin 3) ‖w‖‖ := by
      simp only [norm_smul,PiLp.norm_single,Real.norm_eq_abs,abs_norm]
    rw [hrad (t⁻¹ • w),hrad (t⁻¹ • EuclideanSpace.single 0 ‖w‖),hh]
  rw [packet_potential_center_shift]
  refine ⟨integral_nonneg (fun w => mul_nonneg (Coulomb.coulombKernel_nonneg _) (hp w)),?_⟩
  have H := Coulomb.radial_coulomb_integral_le (fixed_scaled_window_integrable g hm ht)
    (by fun_prop) hp hb hfr (sub_ne_zero.mpr hyz)
  rw [fixed_scaled_window_mass g hm ht,mul_one] at H
  exact H

theorem packet_potential_newton_eq (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    {z y : Position} (hsep : packetWidth c r₀ s z≤‖y-z‖) :
    potentialOf (packetKernel g c r₀ s z) y=coulombKernel (y-z) := by
  let t := packetWidth c r₀ s z
  have ht : 0<t := packetWidth_pos hc hr hs z
  have hp (w : Position) : 0≤(t^3)⁻¹*g (t⁻¹ • w)^2 := by positivity
  have hb (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2≤(t^3)⁻¹*(SchwartzMap.seminorm ℝ 0 0 g)^2 :=
    mul_le_mul_of_nonneg_left (Coulomb.schwartz_square_le g _) (by positivity)
  have hfr (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2=
      (t^3)⁻¹*g (t⁻¹ • EuclideanSpace.single 0 ‖w‖)^2 := by
    have hh : ‖t⁻¹ • w‖=‖t⁻¹ • EuclideanSpace.single (0:Fin 3) ‖w‖‖ := by
      simp only [norm_smul,PiLp.norm_single,Real.norm_eq_abs,abs_norm]
    rw [hrad (t⁻¹ • w),hrad (t⁻¹ • EuclideanSpace.single 0 ‖w‖),hh]
  have hfs (w : Position) (hw : t<‖w‖) : (t^3)⁻¹*g (t⁻¹ • w)^2=0 := by
    have hn : 1<‖t⁻¹ • w‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      have hh := (lt_div_iff₀ ht).mpr (by simpa using hw : 1*t<‖w‖)
      simpa only [div_eq_mul_inv,mul_comm] using hh
    simp [hgs _ hn]
  rw [packet_potential_center_shift]
  have hx : y-z≠0 := by intro h; rw [h,norm_zero] at hsep; exact (not_le_of_gt ht) hsep
  have H := Coulomb.radial_coulomb_integral_eq (fixed_scaled_window_integrable g hm ht)
    (by fun_prop) hp hb hfr ht.le hfs hx hsep
  rw [fixed_scaled_window_mass g hm ht,mul_one] at H
  exact H

theorem packet_potential_near_deficit (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2)
    {z y : Position} (hyz : y≠z) :
    0≤coulombKernel (y-z)-potentialOf (packetKernel g c r₀ s z) y ∧
    coulombKernel (y-z)-potentialOf (packetKernel g c r₀ s z) y≤
      (Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
        (fun z => coulombKernel (y-z)) z := by
  have H := packet_potential_newton g hm hrad hc hr hs hyz
  refine ⟨sub_nonneg.mpr H.2,?_⟩
  by_cases hz : z∈Metric.closedBall y (2*packetWidth c r₀ s y)
  · rw [Set.indicator_of_mem hz]
    linarith [H.1]
  · rw [Set.indicator_of_notMem hz]
    have hd : 2*packetWidth c r₀ s y<‖z-y‖ := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz
    have hl := packetWidth_lipschitz hc.le hr hs z y
    have hi := mul_le_mul_of_nonneg_right hq (norm_nonneg (z-y))
    have hsep : packetWidth c r₀ s z≤‖y-z‖ := by
      rw [norm_sub_rev]
      have hle := (le_abs_self (packetWidth c r₀ s z-packetWidth c r₀ s y)).trans hl
      linarith
    rw [packet_potential_newton_eq g hm hrad hgs hc hr hs hsep,sub_self]
end NeutralAtom
end

end
end

end OAI
