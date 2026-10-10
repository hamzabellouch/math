import Mathlib
import OAI.Analysis.AffineBernstein.DualDetCompact

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TranslateDet

lemma hessian_translate {n : ℕ} (f : Space n → ℝ) (a x : Space n) :
    hessian (fun y => f (a+y)) x = hessian f (a+x) := by
  ext i j
  simp only [hessian, fderiv_comp_add_left]
  exact congrArg (fun D : Space n →L[ℝ] ℝ => D (coordinateVector n i))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => fderiv ℝ f y (coordinateVector n j)) a)

lemma tangentHeight_translate {n : ℕ} (f : Space n → ℝ) (a x y : Space n) :
    tangentHeight (fun z => f (a+z)) x y = tangentHeight f (a+x) (a+y) := by
  simp only [tangentHeight, fderiv_comp_add_left, add_sub_add_left_eq_sub]

lemma affineMaximalOn_translate {n : ℕ} {O : Set (Space n)} {f : Space n → ℝ}
    (hm : AffineMaximalOn O f) (a : Space n) :
    AffineMaximalOn ((fun x => a+x) ⁻¹' O) (fun x => f (a+x)) := by
  have hw : affineWeight (fun x => f (a+x)) = fun x => affineWeight f (a+x) := by
    ext x
    simp only [affineWeight,hessian_translate]
  intro x hx
  simpa only [cofactorHessian,hessian_translate,hw] using hm (a+x) hx

lemma sectionModulus_translate {n : ℕ} {O : Set (Space n)} {f : Space n → ℝ}
    {b : ℝ → ℝ} (hmod : HasLowerSectionModulus O f b) (a : Space n) :
    HasLowerSectionModulus ((fun x => a+x) ⁻¹' O) (fun x => f (a+x)) b := by
  intro x hx r hr y hy
  have hs : a+y ∈ tangentSection O f (a+x) (b r) := by
    refine ⟨hy.1,?_⟩
    have H : tangentHeight (fun z => f (a+z)) x y < b r := hy.2
    exact (tangentHeight_translate f a x y) ▸ H
  have H := hmod (a+x) hx r hr hs
  simpa only [Metric.mem_ball,dist_add_left] using H

lemma affineMaximal_det_inverse_upper_at_of_modulus {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (hp : ∀ x ∈ O, (hessian u x).PosDef)
    (hm : AffineMaximalOn O u) {a : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ O) (b : ℝ → ℝ)
    (hb : 0 < b r) (hmod : HasLowerSectionModulus O u b) :
    ((hessian u a).det)⁻¹ ≤
      (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * (b r/2)^2 *
        Real.exp (r^2/(4*(r^2+1))) / (b r/2)^(n+2) := by
  let V := (fun x : Space n => a+x) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_const.add continuous_id)
  have hVc : Convex ℝ V := by
    intro x hx y hy c d hc hd hcd
    change a+(c • x+d • y) ∈ O
    have H := hcv hx hy hc hd hcd
    convert H using 1
    calc
      a+(c • x+d • y) = (c+d) • a+(c • x+d • y) := by rw [hcd,one_smul]
      _ = c • (a+x)+d • (a+y) := by module
  have hv : ContDiffOn ℝ ∞ (fun x => u (a+x)) V :=
    hu.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hpv : ∀ x ∈ V, (hessian (fun y => u (a+y)) x).PosDef := by
    intro x hx
    rw [hessian_translate]
    exact hp _ hx
  have hballs : Metric.closedBall (0:Space n) r ⊆ V := by
    intro x hx
    apply hball
    simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have H := affineMaximal_det_inverse_upper_of_modulus hV hVc hv hpv
    (affineMaximalOn_translate hm a) hr hballs b hb (sectionModulus_translate hmod a)
  simpa only [hessian_translate,add_zero] using H

end TranslateDet


end
end AffineBernstein
end

end OAI
