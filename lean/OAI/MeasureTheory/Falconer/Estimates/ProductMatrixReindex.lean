import OAI.MeasureTheory.Falconer.Estimates.ProductMatrixIntegrand

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable

theorem product_graph_sum_matrix {p m : ℕ} (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ graphNonedgeIndices p m) (j b : ℕ) (plus : Bool)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I.filter (fun e => e.2 = ((j,b),plus)), F e) =
    ∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  rw [← Finset.sum_product',← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => ((e.1.1.1,e.1.2.1),(e.1.1.2,e.1.2.2)))
  · intro e he
    obtain ⟨he,hs⟩ := Finset.mem_filter.mp he
    have hq := (Finset.mem_product.mp (hI he)).1
    simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.mem_product] at hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hq.1.1,hq.2.1⟩,
      Finset.mem_product.mpr ⟨hq.1.2,hq.2.2⟩⟩,?_⟩
    have hi : productMatrixIndex (e.1.1.1,e.1.2.1) (e.1.1.2,e.1.2.2) j b plus = e := by
      exact Prod.ext rfl hs.symm
    rw [hi]
    exact he
  · intro e he f hf heq
    have hs := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (Prod.ext (Prod.ext heq.1.1 heq.2.1) (Prod.ext heq.1.2 heq.2.2)) hs
  · intro pair hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact ⟨productMatrixIndex pair.1 pair.2 j b plus,Finset.mem_filter.mpr ⟨hp',rfl⟩,rfl⟩
  · intro e he
    have hs := (Finset.mem_filter.mp he).2
    have hi : productMatrixIndex (e.1.1.1,e.1.2.1) (e.1.1.2,e.1.2.2) j b plus = e :=
      Prod.ext rfl hs.symm
    exact congrArg F hi.symm

theorem product_graph_sum_bins {p m : ℕ} (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ graphNonedgeIndices p m) {α : Type*} [AddCommMonoid α]
    (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
      ∑ j ∈ Finset.range m, ∑ b ∈ Finset.range m, ∑ plus : Bool,
        ∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
          ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
            if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  have he : (∑ s ∈ ((Finset.range m) ×ˢ (Finset.range m)) ×ˢ (Finset.univ : Finset Bool),
      ∑ e ∈ I.filter (fun e => e.2 = s), F e) = ∑ e ∈ I, F e := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    exact Finset.sum_eq_single_of_mem e.2 (Finset.mem_product.mp (hI he)).2
      (fun s _ hs => by simp [Ne.symm hs]) |>.trans (by simp)
  rw [← he]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro plus _
  simpa only [Finset.sum_product] using product_graph_sum_matrix I hI j b plus F

end PlanarFalconer

end OAI
