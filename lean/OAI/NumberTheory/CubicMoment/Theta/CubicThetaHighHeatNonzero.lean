import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexHeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatSmallNonzero
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace OAI

/-! For each parameter in Re(s)>1, the genuine Fourier heat kernel is
nonzero at some height above two. This removes the possible common-zero
obstruction for compact radial tests. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaComplexHeightIntegral_real (s : ℂ) (A v : ℝ) :
    cubicThetaComplexHeightIntegral s A (v:ℂ)=
      ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-2)*cubicThetaLinearHeat v A t := by
  unfold cubicThetaComplexHeightIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [cubicThetaComplexHeightHeat,cubicThetaLinearHeat]
  congr 1
  rw [show -(v:ℂ)*((t+A/t:ℝ):ℂ)=((-v*t-A*v/t:ℝ):ℂ) by push_cast; ring]
  exact (Complex.ofReal_exp _).symm

lemma cubicThetaComplexHeightIntegral_real_zero_iff (s : ℂ) (A : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaComplexHeightIntegral s A (v:ℂ)=0 ↔
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)=0 := by
  have he := cubicThetaHeat_height_dilation hv A s
  rw [← cubicThetaComplexHeightIntegral_real] at he
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  constructor
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (Complex.cpow_ne_zero_iff.mpr (Or.inl hvc))
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hvc

theorem cubicThetaHighHeat_nonzero {s : ℂ} (hs : 1<s.re) {A : ℝ} (hA : 0<A) :
    ∃ v : ℝ, 2<v ∧ (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)≠0 := by
  by_contra hn
  push Not at hn
  have hzero (v : ℝ) (hv : 2<v) : cubicThetaComplexHeightIntegral s A (v:ℂ)=0 :=
    (cubicThetaComplexHeightIntegral_real_zero_iff s A (by linarith)).mpr (hn v hv)
  have hmap : Tendsto (fun v : ℝ => (v:ℂ)) (𝓝[≠] (3:ℝ)) (𝓝[≠] (3:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      change (v:ℂ)≠3
      exact_mod_cast hv
  have hnear : ∀ᶠ v : ℝ in 𝓝[≠] 3, cubicThetaComplexHeightIntegral s A (v:ℂ)=0 := by
    have he : ∀ᶠ v : ℝ in 𝓝 3, 2<v := (isOpen_Ioi.mem_nhds (by norm_num : (3:ℝ)∈Ioi 2))
    filter_upwards [nhdsWithin_le_nhds he] with v hv
    exact hzero v hv
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 3, cubicThetaComplexHeightIntegral s A z=0 := by
    by_contra hneg
    have hf := hmap.eventually (not_frequently.mp hneg)
    have hc := hf.and hnear
    exact (hc.exists).elim (fun _ h => h.1 h.2)
  have ha : AnalyticOnNhd ℂ (cubicThetaComplexHeightIntegral s A) {z : ℂ | 0<z.re} :=
    fun z hz => cubicThetaComplexHeightIntegral_analytic s hA hz
  have hglobal := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
      (z₀:=(3:ℂ)) (by norm_num) hfreq
  have hnonzero := cubicThetaDualHeat_eventually_nonzero hs hA.le
  have hc : ∀ᶠ v : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hnonzero,self_mem_nhdsWithin] with v hv hpos
    exact hv ((cubicThetaComplexHeightIntegral_real_zero_iff s A hpos).mp (hglobal (by simpa using hpos)))
  exact (hc.exists).elim (fun _ h => h)

end CubicFirstMoment

end

end OAI
