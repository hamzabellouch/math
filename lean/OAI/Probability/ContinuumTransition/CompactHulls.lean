import OAI.Probability.ContinuumTransition.TransformBounds

namespace OAI

universe u_1

section
open scoped Topology
open Set
namespace ContinuumTemperature

lemma isCompact_convexJoin {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {S T : Set E} (hS : IsCompact S) (hT : IsCompact T) :
    IsCompact (convexJoin ℝ S T) := by
  have he : convexJoin ℝ S T =
      (fun p : ℝ × E × E => (1-p.1) • p.2.1+p.1 • p.2.2) '' (Icc (0:ℝ) 1 ×ˢ S ×ˢ T) := by
    ext z
    simp only [mem_convexJoin,segment_eq_image,mem_image,mem_prod,Prod.exists]
    constructor
    · rintro ⟨x,hx,y,hy,c,hc,rfl⟩
      exact ⟨c,x,y,⟨hc,hx,hy⟩,rfl⟩
    · rintro ⟨c,x,y,⟨hc,hx,hy⟩,rfl⟩
      exact ⟨x,hx,y,hy,c,hc,rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (hS.prod hT)).image (by fun_prop)

lemma compact_convexHull_union {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hcS : Convex ℝ S) (hcT : Convex ℝ T) : IsCompact (convexHull ℝ (S ∪ T)) := by
  by_cases hs : S.Nonempty
  · by_cases ht : T.Nonempty
    · rw [hcS.convexHull_union hcT hs ht]
      exact isCompact_convexJoin hS hT
    · rw [not_nonempty_iff_eq_empty.mp ht,union_empty,hcS.convexHull_eq]
      exact hS
  · rw [not_nonempty_iff_eq_empty.mp hs,empty_union,hcT.convexHull_eq]
    exact hT

lemma compact_convexHull_iUnion_fin {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {n : ℕ} (K : Fin n → Set E) (hk : ∀ i, IsCompact (K i)) (hc : ∀ i, Convex ℝ (K i)) :
    IsCompact (convexHull ℝ (⋃ i, K i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ,← convexHull_convexHull_union_right]
    exact compact_convexHull_union (hk 0) (ih _ (fun i => hk i.succ) (fun i => hc i.succ))
      (hc 0) (convex_convexHull _ _)

end ContinuumTemperature
end

end OAI
