import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Consecutive subarcs of an embedded arc have disjoint interiors.
This supplies the separation needed by the smooth joining operation. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem ordered_arc_images_separated {γ : ℝ → N} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hi : InjOn γ (Icc a c))
    (P Q : SmoothCompactArc I N)
    (hP : P.curve '' Icc P.start P.finish = γ '' Icc a b)
    (hQ : Q.curve '' Icc Q.start Q.finish = γ '' Icc b c)
    (hstart : Q.curve Q.start = γ b) :
    ∀ u ∈ Icc P.start P.finish, ∀ v ∈ Ioc Q.start Q.finish,
      P.curve u ≠ Q.curve v := by
  intro u hu v hv he
  obtain ⟨s,hs,hes⟩ := hP.subset ⟨u,hu,rfl⟩
  obtain ⟨t,ht,het⟩ := hQ.subset ⟨v,⟨hv.1.le,hv.2⟩,rfl⟩
  have hst : s = t := hi ⟨hs.1,hs.2.trans hbc⟩ ⟨hab.trans ht.1,ht.2⟩
    (hes.trans (he.trans het.symm))
  have htb : t = b := le_antisymm (hst ▸ hs.2) ht.1
  have hev : Q.curve v = Q.curve Q.start := het.symm.trans ((congrArg γ htb).trans hstart.symm)
  have hv0 := Q.injective ⟨hv.1.le,hv.2⟩
    (left_mem_Icc.mpr Q.start_lt_finish.le) hev
  exact (ne_of_gt hv.1) hv0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
