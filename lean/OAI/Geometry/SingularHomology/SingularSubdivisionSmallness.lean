import OAI.Geometry.SingularHomology.SingularSmallChainSupport
import OAI.Geometry.SingularHomology.SingularSmallNaturality
import OAI.Geometry.SingularHomology.IteratedSubdivision

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X] {ι : Type*}

theorem naturalChainMap_preserves_range (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor) (n : ℕ)
    (z : (realSingularChainComplex X).X n)
    (hz : z ∈ LinearMap.range ((inclusion U).f n).hom) :
    ((S.app (TopCat.of X)).f n).hom z ∈ LinearMap.range ((inclusion U).f n).hom := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨((restrictChainMap U S).f n).hom w, ?_⟩
  exact congrArg (fun f : chains U ⟶ realSingularChainComplex X => (f.f n).hom w)
    (restrictChainMap_inclusion U S)

theorem eventually_mem_range_inclusion_of_generators (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor) (n : ℕ)
    (hgen : ∀ σ : RealSingularSimplex X n, ∃ N : ℕ,
      (((S.app (TopCat.of X)).f n).hom ^ N) (realSingularGenerator σ 1) ∈
        LinearMap.range ((inclusion U).f n).hom)
    (z : (realSingularChainComplex X).X n) :
    ∃ N : ℕ, ∀ k, N ≤ k →
      (((S.app (TopCat.of X)).f n).hom ^ k) z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  let s := ((S.app (TopCat.of X)).f n).hom
  let P := LinearMap.range ((inclusion U).f n).hom
  have hP : ∀ x ∈ P, s x ∈ P := naturalChainMap_preserves_range U S n
  have hg (σ : RealSingularSimplex X n) :
      realSingularGenerator σ 1 ∈ IteratedSubdivision.eventuallyIn s P := by
    obtain ⟨N, hN⟩ := hgen σ
    exact IteratedSubdivision.mem_eventuallyIn_of_pow_mem s P hP hN
  apply realSingularChain_induction (P := fun z => z ∈ IteratedSubdivision.eventuallyIn s P)
    (IteratedSubdivision.eventuallyIn s P).zero_mem
    (fun _ _ hx hy => (IteratedSubdivision.eventuallyIn s P).add_mem hx hy)
    (fun σ r => ?_) z
  have h := (IteratedSubdivision.eventuallyIn s P).smul_mem r (hg σ)
  simpa only [← map_smul, smul_eq_mul, mul_one] using h

theorem end_pow_f_hom (S : singularFunctor ⟶ singularFunctor) (n k : ℕ) :
    (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom =
      (((S.app (TopCat.of X)).f n).hom ^ k) := by
  rw [← IteratedSubdivision.chainIterate_eq_pow]
  exact IteratedSubdivision.chainIterate_f_hom _ _ _

theorem exists_pow_mem_range_inclusion_of_generators (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor)
    (hgen : ∀ (n : ℕ) (σ : RealSingularSimplex X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom
        (realSingularGenerator σ 1) ∈ LinearMap.range ((inclusion U).f n).hom) :
    ∀ (n : ℕ) (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  intro n z
  have hg (σ : RealSingularSimplex X n) : ∃ k : ℕ,
      (((S.app (TopCat.of X)).f n).hom ^ k) (realSingularGenerator σ 1) ∈
        LinearMap.range ((inclusion U).f n).hom := by
    simpa only [end_pow_f_hom] using hgen n σ
  obtain ⟨N, hN⟩ := eventually_mem_range_inclusion_of_generators U S n hg z
  exact ⟨N, by simpa only [end_pow_f_hom] using hN N le_rfl⟩

end Problem340.SingularSmallChains

end

end OAI
