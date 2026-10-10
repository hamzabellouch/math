import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FourierMeanZeroTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Filter Topology Set MeasureTheory
open scoped FourierTransform ContDiff

theorem schwartz_norm_division_smooth {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hzero : (0 : Ambient d) ∉ tsupport g) :
    ContDiff ℝ ∞ (fun x => ‖x‖⁻¹ • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hzero] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy]
    exact smul_zero _
  · exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul (g.contDiffAt ⊤)

def schwartzNormDivision {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hcompact : HasCompactSupport g) (hzero : (0 : Ambient d) ∉ tsupport g) :
    𝓢(Ambient d, ℂ) :=
  (hcompact.smul_left (f := fun x => ‖x‖⁻¹)).toSchwartzMap
    (schwartz_norm_division_smooth g hzero)

theorem schwartzNormDivision_apply {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) (x : Ambient d) :
    schwartzNormDivision g hc hz x = ‖x‖⁻¹ • g x := rfl

theorem schwartzNormDivision_norm_mul {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) (x : Ambient d) :
    ‖x‖ • schwartzNormDivision g hc hz x = g x := by
  rw [schwartzNormDivision_apply]
  erw [smul_smul]
  by_cases hx : x = 0
  · subst x
    simp +instances [image_eq_zero_of_notMem_tsupport hz]
  · erw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem schwartzNormDivision_inverse_mean_zero {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) :
    (∫ x, (𝓕⁻ (schwartzNormDivision g hc hz) : 𝓢(Ambient d, ℂ)) x) = 0 := by
  apply inverse_fourier_mean_zero_of_zero_at_origin
  simp [schwartzNormDivision_apply]

end

end RieszRectifiability

end OAI
