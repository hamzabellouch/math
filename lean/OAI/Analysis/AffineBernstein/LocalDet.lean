import Mathlib
import OAI.Analysis.AffineBernstein.DetCompactBound
import OAI.Analysis.AffineBernstein.TangentShiftCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LocalDetProducer

/-- A quantitative determinant upper producer using only one finite section
modulus and the original PDE. In particular the Hessian determinant is an
output, not an ellipticity hypothesis. -/
lemma affineMaximal_det_upper_of_section_control {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) (hp : ∀ x ∈ O, (hessian f x).PosDef)
    (hm : AffineMaximalOn O f) {a : Space n} {r h M : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
    (hball : Metric.closedBall a (2*r) ⊆ O)
    (hb : ∀ x ∈ O, |f x| ≤ M)
    (hsection : tangentSection O f a (2*h) ⊆ Metric.ball a r) :
    (hessian f a).det ≤
      (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*M/r)^2+1))+(4*M/r)^2))^n * h^2 *
        Real.exp ((4*M/r)^2/(4*((4*M/r)^2+1))) / h^(n+2) := by
  let g := tangentShift f a h
  let Ω := tangentSection O f a h
  let K := Metric.closedBall a r ∩ (tangentHeight f a) ⁻¹' Iic h
  have hsmallball : Metric.closedBall a r ⊆ O :=
    (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hball
  have ha : a ∈ O := hball (Metric.mem_closedBall_self (by linarith))
  have hc : ConvexOn ℝ O f := convexOn_of_hessian_posSemidef hO hcv hf
    (fun x hx => (hp x hx).posSemidef)
  have hcont := continuousOn_tangentHeight hf.continuousOn a
  have hΩ : IsOpen Ω := hcont.isOpen_inter_preimage hO isOpen_Iio
  have hΩr : Ω ⊆ Metric.ball a r := by
    intro x hx
    exact hsection ⟨hx.1,by dsimp [Ω,tangentSection] at hx; linarith [hx.2]⟩
  have hΩK : Ω ⊆ K := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall (hΩr hx),hx.2.le⟩
  have hKV : K ⊆ O := fun _ hx => hsmallball hx.1
  have hK : IsCompact K := (isCompact_closedBall a r).of_isClosed_subset
    ((hcont.mono hsmallball).preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic) inter_subset_left
  have hg : ContDiffOn ℝ ∞ g O := contDiffOn_tangentShift hf a h
  have hpg : ∀ x ∈ O, (hessian g x).PosDef := by
    intro x hx
    dsimp [g]
    rw [hessian_tangentShift hO hf a h hx]
    exact hp x hx
  have hmg : AffineMaximalOn Ω g := by
    have hfull := affineMaximalOn_tangentShift hO hf hm a h
    exact fun x hx => hfull x hx.1
  have hneg : ∀ x ∈ Ω, g x < 0 := by
    intro x hx
    dsimp [g,tangentShift]
    exact sub_neg.mpr hx.2
  have hbd : ∀ x ∈ K, x ∉ Ω → g x = 0 := by
    intro x hx hn
    have hlo : h ≤ tangentHeight f a x := by
      by_contra nh
      exact hn ⟨hKV hx,lt_of_not_ge nh⟩
    exact sub_eq_zero.mpr (le_antisymm hx.2 hlo)
  have hgFnorm : ∀ x ∈ Metric.closedBall a r, ‖fderiv ℝ f x‖ ≤ 2*M/r := by
    intro x hx
    apply norm_fderiv_le_of_convex_bounded hc (hsmallball hx)
      ((hf.contDiffAt (hO.mem_nhds (hsmallball hx))).differentiableAt (by simp)) hr hM _ hb
    intro y hy
    apply hball
    rw [Metric.mem_closedBall] at *
    have htri := dist_triangle y x a
    linarith
  have hgrad : ∀ x ∈ Ω, gradientSquared g x ≤ (4*M/r)^2 := by
    intro x hx
    rw [gradientSquared_eq_norm_fderiv]
    have hga := hgFnorm a (Metric.mem_closedBall_self hr.le)
    have hgx := hgFnorm x (Metric.ball_subset_closedBall (hΩr hx))
    have hdiff : ‖fderiv ℝ g x‖ ≤ 4*M/r := by
      dsimp [g]
      rw [fderiv_tangentShift ((hf.contDiffAt (hO.mem_nhds hx.1)).differentiableAt (by simp))]
      exact (norm_sub_le _ _).trans ((add_le_add hgx hga).trans_eq (by ring))
    exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  have hdepth : ∀ x ∈ Ω, -g x ≤ h := by
    intro x hx
    have hn := tangentHeight_nonneg hO hcv hf hp ha hx.1
    dsimp [g,tangentShift]
    linarith
  have haΩ : a ∈ Ω := ⟨ha,by simpa using hh⟩
  have habase : h ≤ -g a := by simp [g,tangentShift]
  have hbnd := affineMaximal_det_upper_on_compact_section hO hΩ hK hΩK hKV hg hpg hmg
    hneg hbd (sq_nonneg (4*M/r)) hh.le hh hgrad hdepth haΩ habase
  rwa [hessian_tangentShift hO hf a h ha] at hbnd

end LocalDetProducer


end
end AffineBernstein
end

end OAI
