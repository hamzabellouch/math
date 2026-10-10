import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositivePoleScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroWindow

namespace OAI

/-! Mellin windows at an arbitrary strictly positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveWindow_support (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : tsupport (star W)⊆Ioi (0:ℝ) := by
  have hs : tsupport (star W)⊆Ici ε := by
    apply closure_minimal ?_ isClosed_Ici
    intro v hv
    by_contra hn
    apply hv
    change star (W v)=0
    rw [hW v (le_of_not_ge hn),star_zero]
  intro v hv
  exact lt_of_lt_of_le hε (hs hv)

lemma cubicThetaPositiveWindow_entire (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Differentiable ℂ (mellin (star W)) :=
  smooth_mellin_entire (star W) (star W).hasCompactSupport
    (cubicThetaPositiveWindow_support W hε hW) (star W).continuous

lemma cubicThetaPositiveWindow_power (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (a : ℂ) :
    (∫ v in Ioi ε,star (W v)*(v:ℂ)^a/(v:ℂ)^3)=mellin (star W) (a-2) := by
  have he : (∫ v in Ioi ε,star (W v)*(v:ℂ)^a/(v:ℂ)^3)=
      ∫ v in Ioi (0:ℝ),star (W v)*(v:ℂ)^a/(v:ℂ)^3 := by
    simpa only [div_mul_eq_mul_div] using
      cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW (fun v => (v:ℂ)^a)
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^a/(v:ℂ)^3=(v:ℂ)^(a-2-1) := by
    rw [←Complex.cpow_natCast,←Complex.cpow_sub _ _ hv0]
    congr 1
    ring
  change star (W v)*(v:ℂ)^a/(v:ℂ)^3=(v:ℂ)^(a-2-1)*star (W v)
  rw [mul_div_assoc,hp,mul_comm]

lemma cubicThetaPositiveWindow_power_integrable (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (a : ℂ) :
    IntegrableOn (fun v => star (W v)*(v:ℂ)^a/(v:ℂ)^3) (Ioi ε) := by
  have hm := smooth_mellin_convergent (star W) (star W).hasCompactSupport
    (cubicThetaPositiveWindow_support W hε hW) (star W).continuous (a-2)
  apply (hm.mono_set (Ioi_subset_Ioi hε.le)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hε.trans hv).ne'
  change (v:ℂ)^(a-2-1)*star (W v)=star (W v)*(v:ℂ)^a/(v:ℂ)^3
  rw [mul_div_assoc,←Complex.cpow_natCast,←Complex.cpow_sub _ _ hv0]
  rw [show a-2-1=a-(3:ℕ) by norm_num; ring]
  ring

end CubicFirstMoment

end

end OAI
