import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricFreeMap
import OAI.AlgebraicGeometry.Seshadri.Geometry.FreePresentation
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricSpan

namespace OAI


                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M]

lemma laurentSupported_inter (S U : Set (ℤ × ℤ)) :
    laurentSupported (K := K) (S ∩ U) = laurentSupported S ⊓ laurentSupported U := by
  simp only [laurentSupported,Finsupp.supported_inter,Submodule.comap_inf]

def vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M) :
    Submodule K (cycles A B C) :=
  boundaries A B C ((V 0).comap (A ⊓ B).subtype)
    ((V 1).comap (A ⊓ C).subtype) ((V 2).comap (B ⊓ C).subtype)

lemma edgeAB_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(A ⊓ B)) (hx : (x : M) ∈ V 0) : edgeAB A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

lemma edgeAC_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(A ⊓ C)) (hx : (x : M) ∈ V 1) : edgeAC A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

lemma edgeBC_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(B ⊓ C)) (hx : (x : M) ∈ V 2) : edgeBC A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_right
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

variable [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma freeMap_vertex_relations {ι : Type*} [Fintype ι]
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : ι → M) (he : ∀ a, StandardGenerator V n (e a))
    (A B C : Submodule K M)
    (hA : ∀ x ∈ freeA ι, freeMap e x ∈ A)
    (hB : ∀ x ∈ freeB ι, freeMap e x ∈ B)
    (hC : ∀ x ∈ freeC ι (-(n : ℤ)), freeMap e x ∈ C) :
    (fullBoundaries (freeA ι) (freeB ι) (freeC ι (-(n : ℤ)))).map
      (cycleMap ((freeMap e).restrictScalars K) (freeA ι) (freeB ι) (freeC ι (-(n : ℤ)))
        A B C hA hB hC) ≤ vertexBoundaries A B C V := by
  apply cycleMap_fullBoundaries_le
  · intro x
    apply edgeAB_mem_vertexBoundaries
    apply freeMap_supported e (coneA ∩ coneB)
    · exact fun a z hz => standard_vertex_zero V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩
  · intro x
    apply edgeAC_mem_vertexBoundaries
    apply freeMap_supported e (coneA ∩ coneC (-(n : ℤ)))
    · exact fun a z hz => standard_vertex_one V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩
  · intro x
    apply edgeBC_mem_vertexBoundaries
    apply freeMap_supported e (coneB ∩ coneC (-(n : ℤ)))
    · exact fun a z hz => standard_vertex_two V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩

theorem toric_H1_finite (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i)
    (A B C : Submodule K M)
    (hA : ∀ z ∈ coneA, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z ∈ coneB, ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z ∈ coneC 0, ∀ x ∈ C, T (K := K) z • x ∈ C)
    (incA : V 0 ≤ A) (incB : V 0 ≤ B) (incC : V 1 ≤ C)
    (genA : A = monomialSpan (K := K) coneA (g 0)) (genB : B = monomialSpan (K := K) coneB (g 0))
    (genC : C = monomialSpan (K := K) (coneC 0) (g 1)) :
    Module.Finite K ((cycles A B C) ⧸ vertexBoundaries A B C V) := by
  classical
  obtain ⟨n,hn⟩ := exists_standard_generators V stable g hg clear
  let e : (Σ i, ι i) → M := fun a => T (K := K) (n • weight a.1) • g a.1 a.2
  have he (a : Σ i, ι i) : StandardGenerator V n (e a) := hn a.1 a.2
  have fA : ∀ x ∈ freeA (K := K) (Σ i, ι i), freeMap e x ∈ A := by
    intro x hx
    apply freeMap_supported e coneA A
    · intro a z hz
      exact hA z hz _ (incA (standard_at_zero V n (e a) (he a)))
    · exact fun a => hx a (Set.mem_univ a)
  have fB : ∀ x ∈ freeB (K := K) (Σ i, ι i), freeMap e x ∈ B := by
    intro x hx
    apply freeMap_supported e coneB B
    · intro a z hz
      exact hB z hz _ (incB (standard_at_zero V n (e a) (he a)))
    · exact fun a => hx a (Set.mem_univ a)
  have fC : ∀ x ∈ freeC (K := K) (Σ i, ι i) (-(n : ℤ)), freeMap e x ∈ C := by
    intro x hx
    apply freeMap_supported e (coneC (-(n : ℤ))) C
    · intro a z hz
      have hz' : z+((n : ℤ),0) ∈ coneC 0 := by
        change z.1+(n : ℤ)+(z.2+0) ≤ 0
        change z.1+z.2 ≤ -(n : ℤ) at hz
        omega
      have hm := hC _ hz' _ (incC (standard_at_one V n (e a) (he a)))
      rw [← mul_smul,← T_add,show z + ((n : ℤ),0) + (-(n : ℤ),0) = z by ext <;> simp] at hm
      exact hm
    · exact fun a => hx a (Set.mem_univ a)
  have e0 (a : ι 0) : e ⟨0,a⟩ = g 0 a := by
    have h : n • weight 0 = (0,0) := by ext <;> simp [weight]
    simp only [e,h]
    rw [show T (K := K) (0,0) = 1 from rfl,one_smul]
  have e1 (a : ι 1) : e ⟨1,a⟩ = T (K := K) ((n : ℤ),0) • g 1 a := by
    have h : n • weight 1 = ((n : ℤ),0) := by ext <;> simp [weight]
    simp only [e,h]
  apply finite_H1_of_free_presentation (freeMap e) (-(n : ℤ)) A B C fA fB fC _ _ _
    (vertexBoundaries A B C V) (freeMap_vertex_relations V stable n e he A B C fA fB fC)
  · intro x hx
    have hs : A ≤ (freeA (K := K) (Σ i, ι i)).map ((freeMap e).restrictScalars K) := by
      rw [genA]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      refine ⟨Pi.single ⟨0,a⟩ (T z),single_monomial_mem coneA _ _ hz,?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e0]
    exact Submodule.mem_map.mp (hs hx)
  · intro x hx
    have hs : B ≤ (freeB (K := K) (Σ i, ι i)).map ((freeMap e).restrictScalars K) := by
      rw [genB]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      refine ⟨Pi.single ⟨0,a⟩ (T z),single_monomial_mem coneB _ _ hz,?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e0]
    exact Submodule.mem_map.mp (hs hx)
  · intro x hx
    have hs : C ≤ (freeC (K := K) (Σ i, ι i) (-(n : ℤ))).map ((freeMap e).restrictScalars K) := by
      rw [genC]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      have hz' : z + (-(n : ℤ),0) ∈ coneC (-(n : ℤ)) := by
        change z.1+ -(n : ℤ)+(z.2+0) ≤ -(n : ℤ)
        change z.1+z.2 ≤ 0 at hz
        omega
      refine ⟨Pi.single ⟨1,a⟩ (T (z+(-(n : ℤ),0))),single_monomial_mem _ _ _ hz',?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e1,← mul_smul,← T_add,
        show z + (-(n : ℤ),0) + ((n : ℤ),0) = z by ext <;> simp]
    exact Submodule.mem_map.mp (hs hx)

end
end MaximalSeshadri.PlaneCech

end


end OAI
