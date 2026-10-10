import OAI.Geometry.NodalSets.Elliptic.FrozenPhaseLemmas
import OAI.Geometry.NodalSets.Elliptic.RescaledCoordinates

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def rescaledPhaseDefect (phi : Coord → ℂ) (L : Coord →L[ℝ] ℂ)
    (N s : ℝ) (x v : Coord) : ℂ :=
  (N:ℂ)*(phi (x+(N*s)⁻¹ • v)-phi x)-(s⁻¹:ℝ) • L v

lemma rescaledPhaseDefect_zero (phi : Coord → ℂ) (L : Coord →L[ℝ] ℂ)
    (N s : ℝ) (x : Coord) : rescaledPhaseDefect phi L N s x 0 = 0 := by
  simp [rescaledPhaseDefect]

lemma rescaledPhaseDefect_hasFDerivAt (phi : Coord → ℂ) (L : Coord →L[ℝ] ℂ)
    {N s : ℝ} (hN : N ≠ 0) (hs : s ≠ 0) (x v : Coord)
    (hp : DifferentiableAt ℝ phi (x+(N*s)⁻¹ • v)) :
    HasFDerivAt (rescaledPhaseDefect phi L N s x)
      (s⁻¹ • (fderiv ℝ phi (x+(N*s)⁻¹ • v)-L)) v := by
  have ha := (hasFDerivAt_id (𝕜 := ℝ) v).const_smul ((N*s)⁻¹)
  have hz := ha.const_add x
  have hd := (((hp.hasFDerivAt.comp v hz).sub_const (phi x)).const_mul (N:ℂ)).sub
    (L.hasFDerivAt.const_smul s⁻¹)
  change HasFDerivAt (rescaledPhaseDefect phi L N s x) _ v at hd
  apply hd.congr_fderiv
  ext u
  simp only [smul_apply,sub_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul,
    smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul]
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  have hsc : (s:ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp

lemma rescaledPhaseDefect_bound (phi : Coord → ℂ) (L : Coord →L[ℝ] ℂ)
    {N s R e : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (hR : 0 ≤ R) (he : 0 ≤ e)
    (x : Coord)
    (hp : ∀ v, ‖v‖ ≤ R → DifferentiableAt ℝ phi (x+(N*s)⁻¹ • v))
    (hb : ∀ v, ‖v‖ ≤ R → ‖fderiv ℝ phi (x+(N*s)⁻¹ • v)-L‖ ≤ e)
    (v : Coord) (hv : ‖v‖ ≤ R) :
    ‖rescaledPhaseDefect phi L N s x v‖ ≤ e*‖v‖ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hd u hu := rescaledPhaseDefect_hasFDerivAt phi L hN0.ne' hs0.ne' x u (hp u hu)
  have hh := norm_sub_le_on_closedBall (rescaledPhaseDefect phi L N s x) 0 R e he
    (fun u hu ↦ (hd u (by simpa using hu)).differentiableAt)
    (fun u hu ↦ by
      rw [(hd u (by simpa using hu)).fderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0)]
      exact (mul_le_mul_of_nonneg_left (hb u (by simpa using hu)) (inv_nonneg.mpr hs0.le)).trans
        (by simpa using mul_le_mul_of_nonneg_right ((inv_le_one₀ hs0).mpr hs) he))
    hR v (by simpa using hv)
  simpa only [rescaledPhaseDefect_zero,sub_zero] using hh

end
end Yau.Geometry

end OAI
