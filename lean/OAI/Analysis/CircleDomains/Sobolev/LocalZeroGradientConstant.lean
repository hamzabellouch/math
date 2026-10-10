import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWeyl
import Mathlib.Analysis.Complex.OpenMapping

namespace OAI

/-! A continuous planar Sobolev function with zero weak gradient on a
connected open set is constant there and on its closure. The proved local
complex Weyl lemma reduces this to the holomorphic open mapping theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem constant_on_closure_of_zero_weak_gradient
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    {U : Set EuclideanPlane} (hU : IsOpen U) (hconn : IsConnected U)
    (hz : ∀ᵐ p ∂volume.restrict U, G p = 0) :
    ∃ c : ℝ, ∀ p ∈ closure U, u p = c := by
  let f : EuclideanPlane → ℂ := fun p => (u p : ℂ)
  let D : PlaneLocalWeakComplex f := {
    realGradient := G
    imagGradient := fun _ => 0
    real_weak := by simpa only [f, Complex.ofReal_re] using hw
    imag_weak := by
      intro i ψ hψ hs hsub
      simp [f]
    real_memLp := hLp
    imag_memLp := fun _ _ => MemLp.zero }
  have hz' : ∀ᵐ p ∂volume, p ∈ U → G p = 0 := by
    exact (ae_restrict_iff' hU.measurableSet).mp hz
  have hcr : ∀ᵐ p ∂volume, p ∈ U →
      D.realGradient p 0 = D.imagGradient p 1 ∧
      D.realGradient p 1 = -D.imagGradient p 0 := by
    filter_upwards [hz'] with p hp hpU
    simp [D, hp hpU]
  have hd := D.holomorphic_on_of_cauchyRiemann (Complex.continuous_ofReal.comp hu) hU hcr
  let V := complexPlaneCoordinates '' U
  have hV : IsOpen V := complexPlaneCoordinates.toHomeomorph.isOpenMap _ hU
  have hcV : IsConnected V := hconn.image _ complexPlaneCoordinates.continuous.continuousOn
  have ha : AnalyticOnNhd ℂ (fun z => f (complexPlaneCoordinates.symm z)) V :=
    fun z hz => hd.analyticAt (hV.mem_nhds hz)
  obtain ⟨c, hc⟩ := ha.eq_const_of_im_eq_const (c₀ := 0) (fun _ _ => rfl) hV hcV
  have hcu : U ⊆ {p | u p = c.re} := by
    intro p hp
    have hh := congrArg Complex.re (hc (complexPlaneCoordinates p) ⟨p, hp, rfl⟩)
    change u p = c.re
    simpa only [f, ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_re] using hh
  exact ⟨c.re, fun p hp => (closure_minimal hcu (isClosed_eq hu continuous_const)) hp⟩

 theorem constant_on_homeomorphic_disk
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    (e : ℂ ≃ₜ EuclideanPlane) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hz : ∀ᵐ p ∂volume.restrict (e '' Metric.closedBall c r), G p = 0) :
    ∃ a : ℝ, ∀ p ∈ e '' Metric.closedBall c r, u p = a := by
  have hU : IsOpen (e '' Metric.ball c r) := e.isOpenMap _ Metric.isOpen_ball
  have hc : IsConnected (Metric.ball c r) :=
    ⟨⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  have hUc : IsConnected (e '' Metric.ball c r) := hc.image _ e.continuous.continuousOn
  have hzU : ∀ᵐ p ∂volume.restrict (e '' Metric.ball c r), G p = 0 :=
    hz.filter_mono (ae_mono (Measure.restrict_mono (image_mono Metric.ball_subset_closedBall) le_rfl))
  obtain ⟨a, ha⟩ := constant_on_closure_of_zero_weak_gradient hu G hw hLp hU hUc hzU
  rw [← e.image_closure, closure_ball c hr.ne'] at ha
  exact ⟨a, ha⟩

end CircleDomainRigidity

end

end OAI
