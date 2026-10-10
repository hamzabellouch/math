import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatMellinBounds

namespace OAI

/-! A uniform bound for the normalized primitive kernel at its pole.
The only inputs are the proved lattice Gaussian estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaPrimitiveKernel_nonneg {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    0 ≤ cubicThetaPrimitiveKernel p s := by
  apply tsum_nonneg
  intro r
  split_ifs
  · exact Real.rpow_nonneg (r.height_pos hp).le _
  · exact le_rfl

theorem cubicThetaPrimitiveKernel_gamma_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℂ × ℝ, 0<p.2 → ∀ s : ℝ, 2<s → s ≤ 3 →
      (s-2)*Real.Gamma s*cubicThetaPrimitiveKernel p s ≤ D := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_small_large
  let H := cubicThetaPrimitiveMellinTailMass
  have hH : 0 ≤ H := cubicThetaPrimitiveMellinTailMass_nonneg
  refine ⟨2*C+5*C*H,by positivity,?_⟩
  intro p hp s hs hs3
  have hf := cubicThetaPrimitiveMellin_integrable hp hs hs3
  have hflo : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioc 0 1) :=
    hf.mono_set Ioc_subset_Ioi_self
  have hfhi := hf.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hglo : IntegrableOn (fun t : ℝ => 2*C*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<s-3))).const_mul _
  have hghi : IntegrableOn (fun t : ℝ => 5*C*(t^2*Real.exp (-t/2))) (Ioi 1) :=
    (cubicThetaPrimitiveMellin_tail_integrable.mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))).const_mul _
  have hlo := setIntegral_mono_on hflo hglo measurableSet_Ioc (fun t ht =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      cubicThetaPrimitiveMellin_low_bound hC ht ((hbound p hp).1 t ht.1)))
  have hhi := setIntegral_mono_on hfhi hghi measurableSet_Ioi (fun t ht =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      cubicThetaPrimitiveMellin_high_bound hC hs3 ht ((hbound p hp).2 t ht.le)))
  rw [integral_const_mul,cubicThetaHeatPole_integral hs] at hlo
  rw [integral_const_mul] at hhi
  change _ ≤ 5*C*H at hhi
  have he : (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t)=
      (∫ t in Ioc (0:ℝ) 1,t^(s-1)*cubicThetaPrimitiveHeat p t)+
        ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hflo hfhi]
  rw [cubicThetaPrimitiveKernel_heat_mellin hp hs] at he
  have hsum := add_le_add hlo hhi
  rw [←he] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ s-2 by linarith)
  have hc : (s-2)*(2*C*(1/(s-2))+5*C*H)=2*C+(s-2)*(5*C*H) := by
    field_simp [show s-2≠0 by linarith]
  rw [hc] at hm
  have hlast : (s-2)*(5*C*H) ≤ 5*C*H := by
    nlinarith [mul_nonneg hC hH]
  nlinarith

theorem cubicThetaPrimitiveKernel_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ s : ℝ in 𝓝[>] 2,
      ∀ p : ℂ × ℝ, 0<p.2 → (s-2)*cubicThetaPrimitiveKernel p s ≤ K := by
  obtain ⟨D,hD,hbound⟩ := cubicThetaPrimitiveKernel_gamma_bound
  refine ⟨2*D,by positivity,?_⟩
  have hG : ∀ᶠ s : ℝ in 𝓝 2,(1/2:ℝ)<Real.Gamma s := by
    have h := cubicThetaRealGamma_continuousAt_two.tendsto.eventually
      (Ioi_mem_nhds (show (1/2:ℝ)<Real.Gamma 2 by norm_num))
    exact h
  have h3 : ∀ᶠ s : ℝ in 𝓝 2,s<3 := Iio_mem_nhds (by norm_num)
  filter_upwards [hG.filter_mono nhdsWithin_le_nhds,
    h3.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hG hs3 hs
  change 2<s at hs
  intro p hp
  have h := hbound p hp s hs hs3.le
  have hnonneg := mul_nonneg (show 0 ≤ s-2 by exact sub_nonneg.mpr hs.le)
    (cubicThetaPrimitiveKernel_nonneg hp s)
  have hm := mul_le_mul_of_nonneg_right hG.le hnonneg
  nlinarith

end CubicFirstMoment

end

end OAI
