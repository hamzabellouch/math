import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Function
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_iteratedFDeriv_dilate_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : 0 < r) (b x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f (r⁻¹ • (z-b))) x‖ ≤
      ‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n := by
  let L : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  have hd : (fun z => f (r⁻¹ • (z-b))) = (fun z => (f ∘ L) (z-b)) := rfl
  rw [hd,iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hf (x-b)
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hL : ‖L‖ ≤ r⁻¹ := by
    calc
      _ = ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
      _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L (x-b))‖ * ∏ _i : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n f (L (x-b))‖ * ‖L‖^n := by simp
    _ ≤ ‖iteratedFDeriv ℝ n f (L (x-b))‖ * (r⁻¹)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL n) (norm_nonneg _)
    _ = _ := by simp [L,div_eq_mul_inv]

lemma norm_iteratedFDeriv_scaled_dilate_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : 0 < r) (A : ℝ) (b x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => A • f (r⁻¹ • (z-b))) x‖ ≤
      |A| * ‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n := by
  have hcomp : ContDiff ℝ ∞ (fun z : E => f (r⁻¹ • (z-b))) :=
    hf.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |A| * (‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dilate_le f hf hr b x n) (abs_nonneg _)
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end

end OAI
