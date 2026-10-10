import OAI.Analysis.HenonEmden.RadialJoint

namespace OAI

section OriginVirial

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma integrable_mul_dilation {n : ℕ} {G ψ : Space n → ℝ}
    (hG : Integrable G) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (R : ℝ) :
    Integrable (fun x => G x*ψ (R⁻¹ • x)) := by
  obtain ⟨M,hM⟩ := hψc.exists_bound_of_continuous hψ
  exact hG.mul_bdd (hψ.comp (continuous_id.const_smul (R⁻¹))).aestronglyMeasurable
    (ae_of_all _ fun x => hM _)

lemma radialDir_inner_cutoff {n : ℕ} (ξ : ContDiffBump (0:Space n)) (R : ℝ) (x : Space n) :
    dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x =
      -w n x*(1-ξ (R⁻¹ • x))-eta n x*dir ξ (R⁻¹ • x) (R⁻¹ • x) := by
  have hξ : ContDiff ℝ 2 (ξ : Space n → ℝ) := ξ.contDiff
  have hξdiff := hξ.differentiable (by norm_num)
  have hηd := (hasFDerivAt_eta n x).differentiableAt
  have hξd : Differentiable ℝ (fun y : Space n => ξ (R⁻¹ • y)) :=
    hξdiff.comp (differentiable_id.const_smul (R⁻¹))
  have he : dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x =
      dir (eta n) x x-dir (fun y => eta n y*ξ (R⁻¹ • y)) x x := by
    have hm : DifferentiableAt ℝ (fun y => eta n y*ξ (R⁻¹ • y)) x := hηd.mul (hξd x)
    unfold dir
    rw [show (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) = eta n-(fun y => eta n y*ξ (R⁻¹ • y)) by rfl,
      fderiv_sub hηd hm]
    rfl
  rw [he,dir_mul hηd (hξd x),radialDir_dilation hξdiff]
  simp only [w,dir]
  ring

lemma IsSolution.weighted_virial {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ((n:ℝ)+B)*weightedEnergy (eta n) u q B-weightedEnergy (w n) u q B =
      -(q+1)*(∫ x, eta n x*source u q B x*dir u x x) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  let ξ : ContDiffBump (0:Space n) := ⟨1,2,by norm_num,by norm_num⟩
  let ψ (x : Space n) := dir ξ x x
  have hψ : Continuous ψ := ((ξ.contDiff : ContDiff ℝ 2 (ξ : Space n → ℝ)).continuous_fderiv (by norm_num)).clm_apply continuous_id
  have hψc : HasCompactSupport ψ := compact_radialDir ξ.hasCompactSupport
  let G (x : Space n) := energyDensity u q B x*(((n:ℝ)+B)*eta n x-w n x)
  let H (x : Space n) := energyDensity u q B x*eta n x
  let J (x : Space n) := eta n x*source u q B x*dir u x x
  have hG : Integrable G := (h.energy_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport
    ((continuous_const.mul (continuous_eta n)).sub (continuous_w n))
    (((compactSupport_eta n).mul_left).sub (compactSupport_w n))
  have hH : Integrable H := (h.energy_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport
    (continuous_eta n) (compactSupport_eta n)
  have hJ : Integrable J := h.integrable_eta_source_radialDir hn hp hq
  have he : ∀ᶠ R : ℝ in 𝓝[>] 0,
      ((∫ x, G x)-(∫ x, G x*ξ (R⁻¹ • x)))-(∫ x, H x*ψ (R⁻¹ • x)) =
        -(q+1)*((∫ x, J x)-(∫ x, J x*ξ (R⁻¹ • x))) := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    obtain ⟨hθ,hθc,hθ0⟩ := cutoff_test_off_origin (contDiff_eta (by omega : 1 ≤ n)) (compactSupport_eta n) ξ hR
    have hh := weighted_virial_off_origin h.regular_u h.positive_u q B (hθ.of_le (by norm_num)) hθc hθ0
    have hL : (∫ x, energyDensity u q B x*(((n:ℝ)+B)*(eta n x-eta n x*ξ (R⁻¹ • x))+
        dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x)) =
        ((∫ x, G x)-(∫ x, G x*ξ (R⁻¹ • x)))-(∫ x,H x*ψ (R⁻¹ • x)) := by
      have hsub : Integrable (fun x => G x-G x*ξ (R⁻¹ • x)) :=
        hG.sub (integrable_mul_dilation hG ξ.continuous ξ.hasCompactSupport R)
      rw [← integral_sub hG (integrable_mul_dilation hG ξ.continuous ξ.hasCompactSupport R),
        ← integral_sub hsub (integrable_mul_dilation hH hψ hψc R)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [radialDir_inner_cutoff]; dsimp only [G,H,ψ]; ring
    have hR' : (∫ x, (eta n x-eta n x*ξ (R⁻¹ • x))*source u q B x*dir u x x) =
        (∫ x, J x)-(∫ x,J x*ξ (R⁻¹ • x)) := by
      rw [← integral_sub hJ (integrable_mul_dilation hJ ξ.continuous ξ.hasCompactSupport R)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [J]; ring
    rwa [hL,hR'] at hh
  have hlimL := ((tendsto_const_nhds (x := ∫ x,G x)).sub (integral_mul_dilation_tendsto_zero hG ξ.continuous ξ.hasCompactSupport)).sub
    (integral_mul_dilation_tendsto_zero hH hψ hψc)
  have hlimR := ((tendsto_const_nhds (x := ∫ x,J x)).sub (integral_mul_dilation_tendsto_zero hJ ξ.continuous ξ.hasCompactSupport)).const_mul (-(q+1))
  have hh : (∫ x, G x) = -(q+1)*(∫ x,J x) := by
    simpa only [sub_zero] using tendsto_nhds_unique hlimL (hlimR.congr' (he.mono fun _ hR => hR.symm))
  rw [← hh]
  have hiη := h.integrable_source_energy_weight hn (continuous_eta n) (compactSupport_eta n)
  have hiw := h.integrable_source_energy_weight hn (continuous_w n) (compactSupport_w n)
  rw [weightedEnergy,weightedEnergy,← integral_const_mul,← integral_sub (hiη.const_mul _) hiw]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  dsimp only [G]
  rw [energyDensity_eq_source_mul h.positive_u q B hx]
  ring

end HenonLaneEmden
end
end OriginVirial

end OAI
