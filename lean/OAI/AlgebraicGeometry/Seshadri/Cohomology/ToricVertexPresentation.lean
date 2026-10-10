import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FreeVertices

namespace OAI


                                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma freeMap_vertex {ι : Type*} [Fintype ι]
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : ι → M) (he : ∀ a, StandardGenerator V n (e a))
    (i : Fin 3) (x : ι → LaurentPlane.Ring K) (hx : x ∈ freeVertex ι (-(n : ℤ)) i) :
    freeMap (K := K) e x ∈ V i := by
  apply freeMap_supported e (twistCone (-(n : ℤ)) i) (V i)
  · intro a z hz
    have hcone : z + n • weight i ∈ vertexCone i := by
      simpa [twistCone] using hz
    have h := stable i (z + n • weight i) hcone _ (he a i)
    rw [← mul_smul,← T_add,add_neg_cancel_right] at h
    exact h
  · exact fun a => hx a (Set.mem_univ a)

theorem toric_free_presentation
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    ∃ n : ℕ, ∃ e : (Σ i, ι i) → M,
      (∀ i x, x ∈ freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i → freeMap (K := K) e x ∈ V i) ∧
      ∀ i x, x ∈ V i → ∃ y ∈ freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i, freeMap (K := K) e y = x := by
  classical
  obtain ⟨n,hn⟩ := exists_standard_generators V stable g hg clear
  let e : (Σ i, ι i) → M := fun a => T (K := K) (n • weight a.1) • g a.1 a.2
  have he (a : Σ i, ι i) : StandardGenerator V n (e a) := hn a.1 a.2
  refine ⟨n,e,freeMap_vertex V stable n e he,?_⟩
  intro i x hx
  have hs : V i ≤ (freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i).map
      ((freeMap (K := K) e).restrictScalars K) := by
    rw [hgen i]
    change Submodule.span K _ ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨a,z,hz,rfl⟩
    refine Submodule.mem_map.mpr
      ⟨Pi.single (⟨i,a⟩ : Σ vertex, ι vertex) (T (z-n • weight i)),?_,?_⟩
    · apply single_monomial_mem
      change z-n • weight i - (-(n : ℤ)) • weight i ∈ vertexCone i
      simpa using hz
    · rw [LinearMap.restrictScalars_apply,freeMap_single]
      change T (K := K) (z-n • weight i) • (T (n • weight i) • g i a) = _
      rw [← mul_smul,← T_add,sub_add_cancel]
  exact Submodule.mem_map.mp (hs hx)
end
end MaximalSeshadri.PlaneCech

end


end OAI
