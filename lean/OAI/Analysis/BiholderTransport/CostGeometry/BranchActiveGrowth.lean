import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.MetricLocalGrowth
import OAI.Analysis.BiholderTransport.CostGeometry.BranchGrowth

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_branch_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • p)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖h‖^2 ≤ cTransform v (riemannianExp x h)-cTransform v x+
        (G (riemannianExp x h,riemannianExp x (T • p))-G (x,riemannianExp x (T • p)))/T := by
  obtain ⟨ι,inst,z,w,hz,_,hw,hsum,heq⟩ := eq_pos_convex_span_of_mem_convexHull hp
  let : Fintype ι := inst
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  have hsub : convexHull ℝ (range z) ⊆ convexHull ℝ (activeLogs (n := n) v x) := convexHull_mono hz
  obtain ⟨s,hTs,hs⟩ := exists_between hT1
  obtain ⟨b,hb,H⟩ := hmtw.finite_branch_cost_growth z w hw hsum
    (fun i => (hz (mem_range_self i)).1) hT hTs hs
    (fun t ht q hq => hID t ht q (hsub hq)) (by simpa only [heq] using hG)
    (by simpa only [heq] using hagree)
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  have hiA := hz (mem_range_self i)
  have hsup := active_split_lower_support hv hiA.1 hiA.2 (hT.trans hTs) hs (riemannianExp x h)
  simp only [normalCost,riemannianExp_zero,heq] at hi
  rw [neg_div] at hsup
  linarith

lemma WeakMTW.active_hull_branch_strict_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • p)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∀ᶠ a in 𝓝 x, a≠x → cTransform v x+G (x,riemannianExp x (T • p))/T <
      cTransform v a+G (a,riemannianExp x (T • p))/T := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_branch_growth hv hp hT hT1 hID hG hagree
  have hh := metric_local_growth_of_normal (n := n)
    (f := fun a => cTransform v a+G (a,riemannianExp x (T • p))/T)
    (b := b) (x := x) (by
      filter_upwards [H] with h hh
      rw [sub_div] at hh
      linarith)
  filter_upwards [hh] with a ha hax
  have hd : 0<dist x a := dist_pos.mpr hax.symm
  have hpos := mul_pos hb (sq_pos_of_pos hd)
  linarith

end WeakMTWTransport

end

end OAI
