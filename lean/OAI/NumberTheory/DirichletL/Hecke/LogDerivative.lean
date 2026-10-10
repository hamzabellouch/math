import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration
import OAI.NumberTheory.DirichletL.Hecke.Origin
import OAI.NumberTheory.DirichletL.IdealLogDerivative

namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs

def poleSubtracted (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then
    -deriv (HeckeOrigin.poleRemoved χ) s / HeckeOrigin.poleRemoved χ s
  else -deriv (LFunction χ) s / LFunction χ s

theorem poleRemoved_ne_zero_boundary (χ : Character) (hχ : χ.residue = 1)
    {s : ℂ} (hs : 1 ≤ s.re) : HeckeOrigin.poleRemoved χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact HeckeOrigin.poleRemoved_one_ne_zero χ hχ
  · rw [HeckeOrigin.poleRemoved_eq χ (by intro h; norm_num [h] at hs) h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re χ hs (Or.inl h1))

theorem poleSubtracted_analyticAt (χ : Character) {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (poleSubtracted χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : poleSubtracted χ = fun z =>
        -deriv (HeckeOrigin.poleRemoved χ) z / HeckeOrigin.poleRemoved χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (HeckeOrigin.poleRemoved_entire χ).analyticAt s
    exact ha.deriv.neg.div ha (poleRemoved_ne_zero_boundary χ hχ hs)
  · have heq : poleSubtracted χ = fun z => -deriv (LFunction χ) z / LFunction χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (LFunction_entire_nonprincipal χ hχ).analyticAt s
    exact ha.deriv.neg.div ha (LFunction_ne_zero_of_one_le_re χ hs (Or.inr hχ))

theorem poleSubtracted_continuousOn (χ : Character) :
    ContinuousOn (poleSubtracted χ) {s : ℂ | 1 ≤ s.re} :=
  fun _ hs => (poleSubtracted_analyticAt χ hs).continuousAt.continuousWithinAt

theorem poleRemoved_deriv (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    deriv (HeckeOrigin.poleRemoved χ) s = LFunction χ s + (s-1)*deriv (LFunction χ) s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have heq : HeckeOrigin.poleRemoved χ =ᶠ[nhds s] (fun z => (z-1)*LFunction χ z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    exact HeckeOrigin.poleRemoved_eq χ
      (by intro h; norm_num [h] at hz) (by intro h; norm_num [h] at hz)
  rw [heq.deriv_eq]
  have hd := (LFunction_differentiableAt χ h0 (Or.inl h1)).hasDerivAt
  have hh := ((hasDerivAt_id s).sub_const 1 |>.mul hd).deriv
  have hfun : ((fun x : ℂ => id x - 1) * LFunction χ) =
      (fun z => (z-1)*LFunction χ z) := rfl
  rw [hfun] at hh
  simpa only [one_mul, id_eq] using hh

theorem coeff_LSeries_eq_poleSubtracted (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = (if χ.residue = 1 then (1 : ℂ)/(s-1) else 0) +
      poleSubtracted χ s := by
  rw [coeff_LSeries_eq χ hs]
  by_cases hχ : χ.residue = 1
  · simp only [hχ, ite_true, poleSubtracted]
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    rw [poleRemoved_deriv χ hs, HeckeOrigin.poleRemoved_eq χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs
    field_simp
    ; ring
  · simp [poleSubtracted, hχ]

end SevenEighths.HeckeLogDerivative

end

end OAI
