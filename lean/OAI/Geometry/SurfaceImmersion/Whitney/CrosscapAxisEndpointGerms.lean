import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisFinishGerm

namespace OAI

/-! Both exterior germs of the actual compact source arc can be made
exact crosscap kernel axes simultaneously, keeping every closed-arc point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_axis_endpoint_germs (cp : SurfaceCrosscapCoordinates f p)
    (cq : SurfaceCrosscapCoordinates f q) (P : SmoothCompactArc planeModel M)
    (hPs : P.curve P.start = p) (hPf : P.curve P.finish = q)
    {V W : Set M} (hV : IsOpen V) (hpV : p ∈ V) (hW : IsOpen W) (hqW : q ∈ W)
    (hleft : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ cp.source.source ∧ cp.source (P.curve u) 0 = 0)
    (hright : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ W →
      P.curve u ∈ cq.source.source ∧ cq.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e₀ e₁ : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e₀ ∧ ContDiff ℝ ∞ e₀.symm ∧ e₀ P.start = 0 ∧
      ContDiff ℝ ∞ e₁ ∧ ContDiff ℝ ∞ e₁.symm ∧ e₁ P.finish = 0 ∧
      R.curve =ᶠ[𝓝 P.start] cp.axisCurve ∘ e₀ ∧
      R.curve =ᶠ[𝓝 P.finish] cq.axisCurve ∘ e₁ := by
  obtain ⟨Q,e₀,hQs,hQf,hQP,h₀s,h₀i,h₀0,hQe,_⟩ := crosscap_axis_start_germ cp P hPs hV hpV hleft
  have hQq : Q.curve Q.finish = q := by
    rw [hQf,hQP (right_mem_Icc.mpr P.start_lt_finish.le),hPf]
  have hQright : ∀ u ∈ Icc Q.start Q.finish, Q.curve u ∈ W →
      Q.curve u ∈ cq.source.source ∧ cq.source (Q.curve u) 0 = 0 := by
    intro u hu huW
    rw [hQs,hQf] at hu
    rw [hQP hu] at huW ⊢
    exact hright u hu huW
  obtain ⟨R,e₁,hRs,hRf,hRQ,h₁s,h₁i,h₁0,hRe,hRold⟩ := crosscap_axis_finish_germ cq Q hQq hW hqW hQright
  have hRP : EqOn R.curve P.curve (Icc P.start P.finish) := by
    intro u hu
    have huQ : u ∈ Icc Q.start Q.finish := by rwa [hQs,hQf]
    exact (hRQ huQ).trans (hQP hu)
  refine ⟨R,e₀,e₁,hRs.trans hQs,hRf.trans hQf,hRP,h₀s,h₀i,h₀0,h₁s,h₁i,?_,?_,?_⟩
  · rwa [hQf] at h₁0
  · rw [hQs] at hRold
    exact hRold.trans hQe
  · rwa [hQf] at hRe

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
