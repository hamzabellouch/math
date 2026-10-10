import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridAnalytic

namespace OAI

/-! The spectral equation for actual finite Eisenstein partial sums.
Coordinate analyticity justifies every differentiation of the finite sum. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace CubicFirstMoment

private lemma deriv_sum_apply {ι : Type*} {S : Finset ι} {f : ι → ℝ → ℂ} {x : ℝ}
    (h : ∀ i ∈ S, DifferentiableAt ℝ (f i) x) :
    deriv (fun t : ℝ => ∑ i ∈ S, f i t) x=∑ i ∈ S, deriv (f i) x := by
  have he : (fun t : ℝ => ∑ i ∈ S, f i t)=∑ i ∈ S, f i := by
    funext t
    simp only [Finset.sum_apply]
  rw [he]
  exact deriv_sum h

lemma cubicThetaHyperbolicOperator_sum {ι : Type*} (S : Finset ι)
    (F : ι → ℝ → ℝ → ℝ → ℂ)
    (hF : ∀ i ∈ S, ∀ x y v, 0<v → CubicThetaCoordinateAnalytic (F i) x y v)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun a b t => ∑ i ∈ S, F i a b t) x y v=
      ∑ i ∈ S, cubicThetaHyperbolicOperator (F i) x y v := by
  have hx : deriv (fun t : ℝ => ∑ i ∈ S, F i t y v)=
      (fun t : ℝ => ∑ i ∈ S, deriv (fun u : ℝ => F i u y v) t) := by
    funext t
    exact deriv_sum_apply (fun i hi => (hF i hi t y v hv).1.differentiableAt)
  have hy : deriv (fun t : ℝ => ∑ i ∈ S, F i x t v)=
      (fun t : ℝ => ∑ i ∈ S, deriv (fun u : ℝ => F i x u v) t) := by
    funext t
    exact deriv_sum_apply (fun i hi => (hF i hi x t v hv).2.1.differentiableAt)
  have hxx : deriv (deriv (fun t : ℝ => ∑ i ∈ S, F i t y v)) x=
      ∑ i ∈ S, deriv (deriv (fun t : ℝ => F i t y v)) x := by
    rw [hx]
    exact deriv_sum_apply (fun i hi => (hF i hi x y v hv).1.deriv.differentiableAt)
  have hyy : deriv (deriv (fun t : ℝ => ∑ i ∈ S, F i x t v)) y=
      ∑ i ∈ S, deriv (deriv (fun t : ℝ => F i x t v)) y := by
    rw [hy]
    exact deriv_sum_apply (fun i hi => (hF i hi x y v hv).2.1.deriv.differentiableAt)
  have ht {w : ℝ} (hw : 0<w) : deriv (fun t : ℝ => ∑ i ∈ S, F i x y t) w=
      ∑ i ∈ S, deriv (fun t : ℝ => F i x y t) w := by
    exact deriv_sum_apply (fun i hi => (hF i hi x y w hw).2.2.differentiableAt)
  have he : deriv (fun t : ℝ => ∑ i ∈ S, F i x y t) =ᶠ[𝓝 v]
      (fun t : ℝ => ∑ i ∈ S, deriv (fun u : ℝ => F i x y u) t) := by
    filter_upwards [eventually_gt_nhds hv] with t ht'
    exact ht ht'
  have hvv : deriv (deriv (fun t : ℝ => ∑ i ∈ S, F i x y t)) v=
      ∑ i ∈ S, deriv (deriv (fun t : ℝ => F i x y t)) v := by
    rw [he.deriv_eq]
    exact deriv_sum_apply (fun i hi => (hF i hi x y v hv).2.2.deriv.differentiableAt)
  unfold cubicThetaHyperbolicOperator
  rw [hxx,hyy,hvv,ht hv]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

def cubicThetaFiniteEisenstein (S : Finset (Eisenstein × Eisenstein))
    (s : ℂ) (x y v : ℝ) : ℂ :=
  ∑ p ∈ S, cubicThetaEisensteinGridTerm p (cubicThetaCartesianPoint x y v) s

theorem cubicThetaFiniteEisenstein_eigenvalue (S : Finset (Eisenstein × Eisenstein))
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (cubicThetaFiniteEisenstein S s) x y v=
      s*(s-2)*cubicThetaFiniteEisenstein S s x y v := by
  unfold cubicThetaFiniteEisenstein
  rw [cubicThetaHyperbolicOperator_sum S
    (fun p a b t => cubicThetaEisensteinGridTerm p (cubicThetaCartesianPoint a b t) s)
    (fun p _ a b t ht => cubicThetaEisensteinGrid_analytic p.1 p.2 s a b ht) x y hv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact cubicThetaEisensteinGrid_eigenvalue p.1 p.2 s x y hv

end CubicFirstMoment

end

end OAI
