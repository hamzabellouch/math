import OAI.Geometry.SingularHomology.SingularSmallChainSupport
import OAI.Geometry.SingularHomology.SimplexSingularCompatibility
import OAI.Geometry.SingularHomology.IteratedSubdivisionMesh

namespace OAI

noncomputable section

namespace Problem340.SingularSmallChains

open SingularSubdivision

variable {X : Type} [TopologicalSpace X] {ι : Type*}

theorem simplexChain_mem_range_inclusion (U : ι → Set X) {n : ℕ}
    (σ : RealSingularSimplex X n) (hσ : ∃ i, Set.range σ ⊆ U i) :
    SingularChainFormulas.simplexChain σ ∈ LinearMap.range ((inclusion U).f n).hom := by
  apply (mem_range_inclusion_iff_supported U n _).mpr
  change (singularChainsFinsuppEquiv X n).symm (realSingularGenerator σ 1) ∈ _
  rw [← singularChainsFinsuppEquiv_single X n σ 1, LinearEquiv.symm_apply_apply]
  exact Finsupp.single_mem_supported ℝ 1 hσ

theorem pushforward_realize_mem_range_inclusion (U : ι → Set X) (k n : ℕ)
    (σ : C(StandardSimplex k, X)) (c : Chains (StandardSimplex k) (n + 1))
    (hc : ∀ w ∈ c.support,
      ∃ i, Set.range (σ.comp (AffineSimplex.simplexRealizeMap w)) ⊆ U i) :
    ((realSingularChainMap σ σ.continuous).f n).hom
      (SimplexSingularRealization.realize k n c) ∈
        LinearMap.range ((inclusion U).f n).hom := by
  classical
  rw [SimplexSingularRealization.realize, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  apply (LinearMap.range ((inclusion U).f n).hom).sum_mem
  intro w hw
  rw [map_smul, SingularChainFormulas.simplexChain_map]
  exact (LinearMap.range ((inclusion U).f n).hom).smul_mem _
    (simplexChain_mem_range_inclusion U _ (hc w hw))

theorem exists_iterated_realize_mem_range_inclusion {I : Type}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (n : ℕ) (σ : RealSingularSimplex X n) :
    ∃ N : ℕ, ∀ k ≥ N,
      ((realSingularChainMap σ σ.continuous).f n).hom
        (SimplexSingularRealization.realize n n
          ((subdivision (simplexCenters n) (n + 1))^[k]
            (generator (standardVertices n)))) ∈
          LinearMap.range ((inclusion U).f n).hom := by
  classical
  obtain ⟨N, hN⟩ := exists_iterated_subdivision_small_images n {σ} U hopen hcover
  refine ⟨N, fun k hk => ?_⟩
  apply pushforward_realize_mem_range_inclusion U n n σ
  exact hN k hk σ (Finset.mem_singleton_self σ)

theorem exists_iterated_realizeInSimplex_mem_range_inclusion {I : Type}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (n : ℕ) (σ : RealSingularSimplex X n) :
    ∃ N : ℕ, ∀ k ≥ N,
      ((realSingularChainMap σ σ.continuous).f n).hom
        (AffineSingularRealization.realizeInSimplex n n
          ((subdivision (simplexCenters n) (n + 1))^[k]
            (generator (standardVertices n)))) ∈
          LinearMap.range ((inclusion U).f n).hom := by
  simpa only [SimplexSingularRealization.realize_eq_realizeInSimplex] using
    exists_iterated_realize_mem_range_inclusion U hopen hcover n σ

end Problem340.SingularSmallChains

end

end OAI
