import OAI.MeasureTheory.Falconer.Measures.MultiscaleDensityPruning

namespace OAI

/-! # Core restrictions and density pruning preserve the original pair-cost ledger -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_core_compl_null (ν : Measure X) (μ : Measure Y) [SFinite μ] (P : Set X) (S : Set Y)
    (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) : (ν.prod μ) (P ×ˢ S)ᶜ = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ ∪ univ ×ˢ Sᶜ) := by
      apply measure_mono
      intro p hp
      by_cases hx : p.1 ∈ P
      · exact Or.inr ⟨mem_univ _,fun hy => hp ⟨hx,hy⟩⟩
      · exact Or.inl ⟨hx,mem_univ _⟩
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ)+(ν.prod μ) (univ ×ˢ Sᶜ) := measure_union_le _ _
    _ = 0 := by simp only [Measure.prod_prod,hP,hS,zero_mul,mul_zero,add_zero]

theorem pair_core_restriction_cost (ν : Measure X) (μ : Measure Y) [SFinite μ] (G : Set (X × Y))
    (P : Set X) (S : Set Y) (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) :
    (ν.prod μ) (G ∩ (P ×ˢ S))ᶜ ≤ (ν.prod μ) Gᶜ := by
  rw [compl_inter]
  exact (measure_union_le _ _).trans_eq (by rw [product_core_compl_null ν μ P S hP hS,add_zero])

theorem density_pruned_pair_cost (ν : Measure X) (μ : Measure Y) [SFinite μ]
    (G : Set (X × Y)) (hG : MeasurableSet G) (Q : ℕ → ι → Set Y)
    (I : ℕ → Finset ι) (J : ℕ) (θ : ℝ≥0∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) :
    (ν.prod μ) (G \ multiscaleFiberBad μ G Q I θ J)ᶜ ≤
      (ν.prod μ) Gᶜ+(J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  have he : (G \ multiscaleFiberBad μ G Q I θ J)ᶜ =
      Gᶜ ∪ multiscaleFiberBad μ G Q I θ J := by
    classical
    ext p
    simp only [mem_compl_iff, mem_sdiff, mem_union]
    tauto
  rw [he]
  exact (measure_union_le _ _).trans
    (add_le_add le_rfl (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ))

end Falconer

end OAI
