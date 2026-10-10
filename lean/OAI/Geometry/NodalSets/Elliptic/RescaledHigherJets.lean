import OAI.Geometry.NodalSets.Elliptic.AffineRescalingJets
import OAI.Geometry.NodalSets.Elliptic.RescaledPhaseDefect

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma iteratedFDeriv_linear_high (L : Coord →L[ℝ] ℂ) (v : Coord) {k : ℕ} (hk : 2 ≤ k) :
    iteratedFDeriv ℝ k L v = 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  apply norm_eq_zero.mp
  rw [show 2+j = (j+1)+1 by omega,← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ ↦ L := by funext z; exact L.fderiv
  rw [he,iteratedFDeriv_succ_const]
  simp

lemma rescaledPhaseDefect_smooth (phi : Coord → ℂ) (L : Coord →L[ℝ] ℂ)
    (N s : ℝ) (x v : Coord) (hp : ContDiffAt ℝ ∞ phi (x+(N*s)⁻¹ • v)) :
    ContDiffAt ℝ ∞ (rescaledPhaseDefect phi L N s x) v := by
  exact (contDiffAt_const.mul ((hp.comp v
    (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt).sub contDiffAt_const)).sub
    (L.contDiff.contDiffAt.const_smul _)

lemma rescaledPhaseDefect_high_bound {U : Set Coord} (hU : IsOpen U)
    (phi : Coord → ℂ) (hp : ContDiffOn ℝ ∞ phi U) (L : Coord →L[ℝ] ℂ)
    {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (x v : Coord)
    (hz : x+(N*s)⁻¹ • v ∈ U) {k : ℕ} (hk : 2 ≤ k) {C : ℝ}
    (hC : 0 ≤ C) (hb : ‖iteratedFDeriv ℝ k phi (x+(N*s)⁻¹ • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (rescaledPhaseDefect phi L N s x) v‖ ≤ C/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hr := (rescaling_radius_bound hN hs).1
  let F : Coord → ℂ := fun z ↦ phi (x+(N*s)⁻¹ • z)
  have hF : ContDiffAt ℝ ∞ F v := (hp.contDiffAt (hU.mem_nhds hz)).comp v
    (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt
  have hkle : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have he : rescaledPhaseDefect phi L N s x =
      (fun z ↦ (N:ℂ) • (F z-phi x)) - (fun z ↦ (s⁻¹ • L) z) := rfl
  rw [he,iteratedFDeriv_sub_apply ((hF.sub contDiffAt_const).const_smul (N:ℂ) |>.of_le hkle)
    ((s⁻¹ • L).contDiff.contDiffAt.of_le hkle),iteratedFDeriv_linear_high _ _ hk,sub_zero,
    iteratedFDeriv_const_smul_apply' ((hF.sub contDiffAt_const).of_le hkle)]
  change ‖(N:ℂ) • iteratedFDeriv ℝ k (F - fun _ ↦ phi x) v‖ ≤ C/N
  rw [iteratedFDeriv_sub_apply (hF.of_le hkle) (contDiffAt_const.of_le hkle),
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simp only [Pi.zero_apply,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN0]
  have ha := affine_rescaling_derivative_power_on hU phi hp x v hr hz k
  calc
    _ ≤ N*(((N*s)⁻¹)^k*C) := mul_le_mul_of_nonneg_left
      (ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))) hN0.le
    _ = (N*((N*s)⁻¹)^k)*C := by ring
    _ ≤ N⁻¹*C := mul_le_mul_of_nonneg_right (radius_high_power hN hs hk) hC
    _ = C/N := by ring

def rescaledAmplitudeRatio (amp : Coord → ℂ) (N s : ℝ) (x v : Coord) : ℂ :=
  amp (x+(N*s)⁻¹ • v)/amp x

lemma rescaledAmplitudeRatio_high_bound {U : Set Coord} (hU : IsOpen U)
    (amp : Coord → ℂ) (ha : ContDiffOn ℝ ∞ amp U)
    {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (x v : Coord)
    (hz : x+(N*s)⁻¹ • v ∈ U) (hax : (1/2:ℝ) ≤ ‖amp x‖)
    {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (_ : 0 ≤ C)
    (hb : ‖iteratedFDeriv ℝ k amp (x+(N*s)⁻¹ • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (rescaledAmplitudeRatio amp N s x) v‖ ≤ 2*C/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hrN : (N*s)⁻¹ ≤ N⁻¹ :=
    (inv_le_inv₀ (mul_pos hN0 (lt_of_lt_of_le zero_lt_one hs)) hN0).mpr (by nlinarith)
  have hp : ((N*s)⁻¹)^k ≤ N⁻¹ :=
    (pow_le_pow_of_le_one hr0 hr1 hk).trans (by simpa using hrN)
  have hF : ContDiffAt ℝ ∞ (fun z ↦ amp (x+(N*s)⁻¹ • z)) v :=
    (ha.contDiffAt (hU.mem_nhds hz)).comp v (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt
  have he : rescaledAmplitudeRatio amp N s x = fun z ↦ (amp x)⁻¹ • amp (x+(N*s)⁻¹ • z) := by
    funext z; simp [rescaledAmplitudeRatio,div_eq_mul_inv,mul_comm]
  rw [he,iteratedFDeriv_const_smul_apply' (hF.of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))),norm_smul,norm_inv]
  have haxi : ‖amp x‖⁻¹ ≤ 2 := by
    have hh := (inv_le_inv₀ (by linarith : 0 < ‖amp x‖) (by norm_num : (0:ℝ) < 1/2)).mpr hax
    norm_num at hh
    exact hh
  have hf := affine_rescaling_derivative_power_on hU amp ha x v hr0 hz k
  calc
    _ ≤ 2*(N⁻¹*C) := mul_le_mul haxi (hf.trans (mul_le_mul hp hb (norm_nonneg _) (inv_nonneg.mpr hN0.le)))
      (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
