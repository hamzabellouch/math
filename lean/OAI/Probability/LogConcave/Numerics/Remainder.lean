import Mathlib
import OAI.Probability.LogConcave.Analysis.SymmetricGradientDerivative
import OAI.Probability.LogConcave.Sampling.Primitive

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
namespace Trapezoid
open scoped RealInnerProductSpace Topology
open Asymptotics

variable {d : ℕ} {H : Point d → ℝ}

def remainder (H : Point d → ℝ) (x y : Point d) : ℝ :=
  H y-H x-inner ℝ (y-x) (gradient H x+gradient H y)/2

lemma contDiff_gradient (hH : ContDiff ℝ 2 H) : ContDiff ℝ 1 (gradient H) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hH.fderiv_right (by norm_num))

lemma hasFDerivAt_remainder (hH : ContDiff ℝ 2 H) (x y : Point d) :
    HasFDerivAt (remainder H x)
      (InnerProductSpace.toDual ℝ (Point d)
        ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x)))) y := by
  have hg := contDiff_gradient hH
  have hd := (hasFDerivAt_id y).sub_const x |>.inner ℝ
    ((hasFDerivAt_const (gradient H x) y).add
      (hg.differentiable (by norm_num) y).hasFDerivAt)
  have hh := ((hH.differentiable (by norm_num) y).hasFDerivAt.sub_const (H x)).sub
    (hd.const_mul (1/2:ℝ))
  convert! hh using 1
  · funext z; dsimp [remainder]; ring
  ext z
  have hs : inner ℝ (fderiv ℝ (gradient H) y (y-x)) z =
      inner ℝ (y-x) (fderiv ℝ (gradient H) y z) :=
    LogConcaveSampling.ContDiff.isSymmetric_gradient_derivative hH y (y-x) z
  have hgrad : fderiv ℝ H y z = inner ℝ (gradient H y) z :=
    InnerProductSpace.toDual_symm_apply.symm
  simp only [InnerProductSpace.toDual_apply_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    fderivInnerCLM_apply, Pi.add_apply, id_eq, zero_add, smul_eq_mul]
  change inner ℝ ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x))) z =
    fderiv ℝ H y z-(1/2:ℝ)*(inner ℝ (y-x) (fderiv ℝ (gradient H) y z)+
      inner ℝ z (gradient H x+gradient H y))
  rw [real_inner_smul_left,inner_sub_left,inner_sub_left,hgrad,← hs,inner_add_right]
  nlinarith [real_inner_comm z (gradient H x),real_inner_comm z (gradient H y)]

lemma derivative_remainder_littleO (hH : ContDiff ℝ 2 H) (x : Point d) :
    (fun y => InnerProductSpace.toDual ℝ (Point d)
      ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x))))
      =o[𝓝 x] (fun y => ‖y-x‖) := by
  have hg := contDiff_gradient hH
  have hl := (hg.differentiable (by norm_num) x).hasFDerivAt.isLittleO
  have hc := (hg.continuous_fderiv (by norm_num)).continuousAt (x := x)
  rw [Asymptotics.isLittleO_iff]
  intro c hcpos
  have he₁ := hl.bound hcpos
  have he₂ : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x‖ < c := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hc c hcpos)
  filter_upwards [he₁,he₂] with y hy hz
  rw [LinearIsometryEquiv.norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),norm_norm]
  have hid : gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x) =
      (gradient H y-gradient H x-fderiv ℝ (gradient H) x (y-x))-
      (fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x) (y-x) := by
    simp only [sub_apply]; abel
  rw [hid]
  have hb := norm_sub_le (gradient H y-gradient H x-fderiv ℝ (gradient H) x (y-x))
    ((fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x) (y-x))
  have hh := (fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x).le_opNorm (y-x)
  have hc' := mul_le_mul_of_nonneg_right hz.le (norm_nonneg (y-x))
  nlinarith only [hy,hb,hh,hc']

theorem remainder_littleO (hH : ContDiff ℝ 2 H) (x : Point d) :
    remainder H x =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  have hl := derivative_remainder_littleO hH x
  have hh := convex_univ.isLittleO_pow_succ (n := 1) (Set.mem_univ x)
    (fun y _ => (hasFDerivAt_remainder hH x y).hasFDerivWithinAt)
    (by simpa only [nhdsWithin_univ,pow_one] using hl)
  change (fun y => H y-H x-inner ℝ (y-x) (gradient H x+gradient H y)/2) =o[𝓝 x] (fun y => ‖y-x‖^2)
  simpa [remainder] using hh

lemma remainder_bound (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (x y : Point d) :
    |remainder H x y| ≤ (M:ℝ)*‖y-x‖^2 := by
  have ht := quadratic_remainder_of_gradient_lipschitz hH hM x (y-x)
  rw [add_sub_cancel] at ht
  have hnorm : ‖gradient H y-gradient H x‖ ≤ (M:ℝ)*‖y-x‖ := hM.norm_sub_le y x
  have hi := (abs_real_inner_le_norm (y-x) (gradient H y-gradient H x)).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg (y-x)))
  have he : remainder H x y =
      (H y-H x-inner ℝ (y-x) (gradient H x))-
        inner ℝ (y-x) (gradient H y-gradient H x)/2 := by
    dsimp [remainder]
    rw [inner_add_right,inner_sub_right]
    ring
  rw [he]
  have hb := abs_sub (H y-H x-inner ℝ (y-x) (gradient H x))
    (inner ℝ (y-x) (gradient H y-gradient H x)/2)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  nlinarith only [hb,ht,hi]

end Trapezoid
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
