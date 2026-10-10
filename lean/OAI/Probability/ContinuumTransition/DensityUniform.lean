import OAI.Probability.ContinuumTransition.DensityBounds

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma physical_coefficient_lower {t β m : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hm : 17576*kernelHeight*m ≤ t) :
    β*t/1024 ≤ (β*((t^2/8-2197*t*kernelHeight*m/2)/64)/t) := by
  apply (le_div_iff₀ ht).mpr
  have hh := mul_le_mul_of_nonneg_left hm ht.le
  have hh' : t^2/16 ≤ t^2/8-2197*t*kernelHeight*m/2 := by nlinarith only [hh]
  have hh'' := mul_le_mul_of_nonneg_left hh' hβ
  nlinarith only [hh'']

lemma bounded_density_of_quadratic {t β h a H P d : ℝ}
    (ht : 1 ≤ t) (hβ : 1/4 ≤ β) (hβ' : β ≤ 2) (hh : h ≤ 10)
    (ha : 1024*a ≤ t) (hd : 0 ≤ d) (hP : 0 ≤ P)
    (hH : β*t/1024*d^2-(β*t/2)*d-1/t ≤ H)
    (he : P = h*d+β*a*d^2/2-H) : d ≤ 1048576 := by
  have ht0 : 0 < t := by linarith
  have hc : t/8192 ≤ β*t/1024-β*a/2 := by
    have hh1 := mul_le_mul_of_nonneg_left ha (show 0 ≤ β by linarith)
    have hh2 := mul_le_mul_of_nonneg_right hβ ht0.le
    nlinarith only [hh1,hh2]
  have hlin : h+β*t/2 ≤ 11*t := by
    have hh1 := mul_le_mul_of_nonneg_right hβ' ht0.le
    nlinarith only [hh,hh1,ht]
  have hinv : 1/t ≤ t := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [sq_nonneg (t-1),ht]
  have hh0 := mul_le_mul_of_nonneg_right hc (sq_nonneg d)
  have hh1 := mul_le_mul_of_nonneg_right hlin hd
  have hquad : t*(d^2/8192-11*d-1) ≤ 0 := by nlinarith only [hh0,hh1,hinv,hH,hP,he]
  have hquad' : d^2/8192-11*d-1 ≤ 0 := by
    by_contra hn
    have hh := mul_pos ht0 (lt_of_not_ge hn)
    linarith only [hh,hquad]
  by_contra hn
  have hg : 1048576 < d := lt_of_not_ge hn
  have hh := mul_nonneg hd (le_of_lt (sub_pos.mpr hg))
  nlinarith only [hquad',hg,hh]

lemma meanField_ge_base {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x : Parameter} (hx : x ∈ pressureDomain) : Q x ≤ P x := by
  have hh := (hP x hx).1 (mem_range_self (0:ℝ))
  simpa only [quadraticCost,shiftedField,mul_zero,add_zero,zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero,Prod.mk.eta] using hh

lemma active_pressure_gap {Q P : Parameter → ℝ} {H : ℝ → ℝ → ℝ} {a D : ℝ}
    (hH : IsPartialConjugate Q H)
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h)))
    (hQ : ∀ β, 0 < β → ∀ h, IsLUB ((fun d => h*d-H β d) '' Ici 0) (Q (β,h)))
    {x w : Parameter} (hx : x ∈ pressureDomain) (ha : 0 ≤ a)
    (hw : w ∈ activeLifts Q a P x) (hd : w.2 ≤ D) : P x ≤ Q x+x.1*a*D^2/2 := by
  have hd0 := active_density_nonneg hm hx hw
  have he := active_canonical_eq hH hm hx hw
  have hl := (hQ x.1 hx x.2).1 (mem_image_of_mem (fun d => x.2*d-H x.1 d) hd0)
  have hs : w.2^2 ≤ D^2 := sq_le_sq₀ hd0 (hd0.trans hd) |>.mpr hd
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg (le_of_lt hx) ha)
  nlinarith only [he,hl,hmul]

end ContinuumTemperature
end
end

end OAI
