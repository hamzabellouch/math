import Mathlib
import OAI.Analysis.AffineBernstein.DetInteriorBall
import OAI.Analysis.AffineBernstein.EntireGraphComplete

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedFamilyDet

lemma tangentHeight_tangentShift {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (a x y : Space n) (h : ℝ) :
    tangentHeight (tangentShift v a h) x y = tangentHeight v x y := by
  simp only [tangentHeight, tangentShift, fderiv_tangentShift (hv x),
    sub_apply, map_sub]
  ring

/-- All normalized solutions have the same determinant bounds on the fixed
inner ball. The constants precede the function; no local analytic estimate
is postulated. -/
theorem normalized_balanced_det_bounds {n : ℕ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v : Space n → ℝ,
      ContDiff ℝ ∞ v → (∀ x, (hessian v x).PosDef) →
      AffineMaximalOn univ v → v 0=0 → fderiv ℝ v 0=0 →
      SectionBalance univ v ρ →
      Metric.ball 0 1 ⊆ tangentSection univ v 0 1 →
      tangentSection univ v 0 1 ⊆ Metric.ball 0 R →
      ∀ x ∈ Metric.ball (0:Space n) (1/8:ℝ),
        c ≤ (hessian v x).det ∧ (hessian v x).det ≤ C := by
  obtain ⟨c,C,hc,hC,H⟩ := normalized_det_interior_ball_producer n (normalizedModulus ρ R)
    (fun _ _ => normalizedModulus_pos hρ)
  refine ⟨c,C,hc,hC,?_⟩
  intro v hv hp hm hv0 hdv0 hbal hin hout
  let f := tangentShift v 0 1
  have hf := contDiffOn_tangentShift hv.contDiffOn 0 1 (Ω := Metric.ball 0 (1/4:ℝ))
  have he (x : Space n) : f x = v x-1 := by simp [f,tangentShift,tangentHeight,hv0,hdv0]
  have hh (x : Space n) : hessian f x = hessian v x :=
    hessian_tangentShift isOpen_univ hv.contDiffOn 0 1 (mem_univ x)
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hv.contDiffOn
    (fun x _ => (hp x).posSemidef)
  have hm' : AffineMaximalOn (Metric.ball 0 (1/4:ℝ)) f :=
    fun x _ => affineMaximalOn_tangentShift isOpen_univ hv.contDiffOn hm 0 1 x (mem_univ x)
  have hfb (x : Space n) (hx : x ∈ Metric.ball 0 (1/4:ℝ)) : -1 ≤ f x ∧ f x ≤ 0 := by
    rw [he]
    have hlo : 0 ≤ v x := by
      have H := tangentHeight_nonneg isOpen_univ convex_univ hv.contDiffOn
        (fun z _ => hp z) (mem_univ 0) (mem_univ x)
      simpa only [tangentHeight,hv0,hdv0,sub_zero,zero_apply] using H
    have hhi := normalized_value_le_quarter hcv hv0 hdv0 hin (mem_ball_zero_iff.mp hx)
    constructor <;> linarith
  have hmod : HasLowerSectionModulus (Metric.ball 0 (1/4:ℝ)) f (normalizedModulus ρ R) := by
    intro x hx r hr y hy
    apply normalized_modulus_of_sectionBalance hv hp (euclideanGraphComplete_entire hv)
      hv0 hdv0 hρ hρ1 hR hbal hin hout hx hr
    refine ⟨mem_univ y,?_⟩
    have HH : tangentHeight f x y < normalizedModulus ρ R r := hy.2
    dsimp only [f] at HH
    rwa [tangentHeight_tangentShift (hv.differentiable (by simp))] at HH
  intro x hx
  simpa only [hh] using H f hf (fun x _ => hh x ▸ hp x) hm' hfb hmod x hx

end NormalizedFamilyDet


end
end AffineBernstein
end

end OAI
