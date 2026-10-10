import OAI.Analysis.CircleDomains.Topology.PlanarRectangleGreen
import OAI.Analysis.CircleDomains.Topology.PlanarMapChangeVariables
import OAI.Analysis.CircleDomains.Modulus.RegularCurveNormalStrip

namespace OAI

/-! The rectangle identity on either side of a regular boundary arc.
Three sides vanish for forms localized inside the normal chart. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma normal_strip_base_form {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (P Q : ℂ → ℝ) (t : ℝ) :
    pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (t,0) =
      P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  simp only [pulledPlanarForm,curveNormalStrip_fderiv hγ,
    one_smul,zero_smul,add_zero,curveNormalStrip]

lemma pulledPlanarForm_eq_zero {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    {p v : ℝ × ℝ} (hP : P (F p) = 0) (hQ : Q (F p) = 0) :
    pulledPlanarForm P Q F v p = 0 := by
  simp only [pulledPlanarForm,hP,hQ,zero_mul,zero_add]

lemma normal_strip_upper_green {P Q : ℂ → ℝ} {γ : ℝ → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hγ : ContDiff ℝ ∞ γ)
    (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R)
    (hl : ∀ y ∈ uIcc 0 R, P (curveNormalStrip γ (a,y)) = 0 ∧
      Q (curveNormalStrip γ (a,y)) = 0)
    (hr : ∀ y ∈ uIcc 0 R, P (curveNormalStrip γ (b,y)) = 0 ∧
      Q (curveNormalStrip γ (b,y)) = 0)
    (ht : ∀ x ∈ uIcc a b, P (curveNormalStrip γ (x,R)) = 0 ∧
      Q (curveNormalStrip γ (x,R)) = 0) :
    (∫ p in Icc (a,0) (b,R), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
      ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
        (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) =
      ∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  have hh := integral_pulledPlanarForm_curl_rectangle hP hQ
    (curveNormalStrip_contDiff hγ) (a,0) (b,R) ⟨hab,hR⟩
  have hzright : (∫ y in 0..R,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (b,y)) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hr y hy).1 (hr y hy).2
      _ = 0 := by simp
  have hzleft : (∫ y in 0..R,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (a,y)) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hl y hy).1 (hl y hy).2
      _ = 0 := by simp
  have hztop : (∫ x in a..b,
      pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (x,R)) = 0 := by
    calc
      _ = ∫ _x in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact pulledPlanarForm_eq_zero (ht x hx).1 (ht x hx).2
      _ = 0 := by simp
  change (∫ p in Icc (a,0) (b,R), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
    ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
      (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) = _ at hh
  rw [hzright,hzleft,hztop,add_zero,sub_zero,sub_zero] at hh
  rw [hh]
  apply intervalIntegral.integral_congr
  intro t _
  exact normal_strip_base_form hγ P Q t

lemma normal_strip_lower_green {P Q : ℂ → ℝ} {γ : ℝ → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hγ : ContDiff ℝ ∞ γ)
    (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R)
    (hl : ∀ y ∈ uIcc (-R) 0, P (curveNormalStrip γ (a,y)) = 0 ∧
      Q (curveNormalStrip γ (a,y)) = 0)
    (hr : ∀ y ∈ uIcc (-R) 0, P (curveNormalStrip γ (b,y)) = 0 ∧
      Q (curveNormalStrip γ (b,y)) = 0)
    (hb : ∀ x ∈ uIcc a b, P (curveNormalStrip γ (x,-R)) = 0 ∧
      Q (curveNormalStrip γ (x,-R)) = 0) :
    (∫ p in Icc (a,-R) (b,0), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
      ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
        (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) =
      -(∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  have hh := integral_pulledPlanarForm_curl_rectangle hP hQ
    (curveNormalStrip_contDiff hγ) (a,-R) (b,0) ⟨hab,neg_nonpos.mpr hR⟩
  have hzright : (∫ y in (-R)..0,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (b,y)) = 0 := by
    calc
      _ = ∫ _y in (-R)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hr y hy).1 (hr y hy).2
      _ = 0 := by simp
  have hzleft : (∫ y in (-R)..0,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (a,y)) = 0 := by
    calc
      _ = ∫ _y in (-R)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hl y hy).1 (hl y hy).2
      _ = 0 := by simp
  have hzbottom : (∫ x in a..b,
      pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (x,-R)) = 0 := by
    calc
      _ = ∫ _x in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact pulledPlanarForm_eq_zero (hb x hx).1 (hb x hx).2
      _ = 0 := by simp
  change (∫ p in Icc (a,-R) (b,0), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
    ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
      (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) = _ at hh
  rw [hzright,hzleft,hzbottom,add_zero,zero_sub,sub_zero] at hh
  rw [hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact normal_strip_base_form hγ P Q t

end CircleDomainRigidity

end

end OAI
