import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneFreeCech

namespace OAI


                                           
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M]

def weight : Fin 3 → ℤ × ℤ := ![(0,0),(1,0),(0,1)]
def vertexCone : Fin 3 → Set (ℤ × ℤ) :=
  ![coneA ∩ coneB,coneA ∩ coneC 0,coneB ∩ coneC 0]

lemma direction_mem (i j : Fin 3) (n : ℕ) : n • (weight j - weight i) ∈ vertexCone i := by
  fin_cases i <;> fin_cases j <;> simp [weight,vertexCone,coneA,coneB,coneC]

lemma vertexCone_add (i : Fin 3) {z w : ℤ × ℤ}
    (hz : z ∈ vertexCone i) (hw : w ∈ vertexCone i) : z+w ∈ vertexCone i := by
  fin_cases i <;> simp [vertexCone,coneA,coneB,coneC] at * <;> omega

lemma clearing_monotone (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (i j : Fin 3) (x : M) {n d : ℕ} (hd : d ≤ n)
    (hx : T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    T (K := K) (n • (weight j-weight i)) • x ∈ V i := by
  have he : n • (weight j-weight i) = (n-d) • (weight j-weight i) + d • (weight j-weight i) := by
    rw [← add_nsmul,Nat.sub_add_cancel hd]
  rw [he,T_add,mul_smul]
  exact stable i _ (direction_mem i j (n-d)) _ hx

theorem exists_standard_generators (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    ∃ n : ℕ, ∀ (j : Fin 3) (a : ι j) (i : Fin 3),
      T (K := K) (-(n • weight i)) • (T (K := K) (n • weight j) • g j a) ∈ V i := by
  classical
  choose d hd using fun (i j : Fin 3) (a : ι j) => clear i j (g j a) (hg j a)
  let n := Finset.univ.sup (fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
  refine ⟨n,?_⟩
  intro j a i
  have hle : d i j a ≤ n := Finset.le_sup (f := fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
    (Finset.mem_univ (i,⟨j,a⟩))
  have he : -(n • weight i) + n • weight j = n • (weight j-weight i) := by
    rw [nsmul_sub]; abel
  rw [← mul_smul,← T_add,he]
  exact clearing_monotone V stable i j (g j a) hle (hd i j a)

def StandardGenerator (V : Fin 3 → Submodule K M) (n : ℕ) (e : M) : Prop :=
  ∀ i, T (K := K) (-(n • weight i)) • e ∈ V i

lemma standard_at_zero (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : e ∈ V 0 := by
  simpa [weight, show T (K := K) (0,0) = 1 from T_zero] using he 0

lemma standard_at_one (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : T (K := K) (-(n : ℤ),0) • e ∈ V 1 := by
  simpa [weight] using he 1

lemma standard_at_two (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : T (K := K) (0,-(n : ℤ)) • e ∈ V 2 := by
  simpa [weight] using he 2

lemma standard_vertex_zero (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneA ∩ coneB) : T (K := K) z • e ∈ V 0 :=
  stable 0 z hz e (standard_at_zero V n e he)

lemma standard_vertex_one (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneA ∩ coneC (-(n : ℤ))) : T (K := K) z • e ∈ V 1 := by
  have h : z + ((n : ℤ),0) ∈ vertexCone 1 := by
    simp [vertexCone,coneA,coneB,coneC] at hz ⊢
    omega
  have heq : z + ((n : ℤ),0) + (-(n : ℤ),0) = z := by ext <;> simp
  have hm := stable 1 _ h _ (standard_at_one V n e he)
  rw [← mul_smul,← T_add,heq] at hm
  exact hm

lemma standard_vertex_two (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneB ∩ coneC (-(n : ℤ))) : T (K := K) z • e ∈ V 2 := by
  have h : z + (0,(n : ℤ)) ∈ vertexCone 2 := by
    simp [vertexCone,coneA,coneB,coneC] at hz ⊢
    omega
  have heq : z + (0,(n : ℤ)) + (0,-(n : ℤ)) = z := by ext <;> simp
  have hm := stable 2 _ h _ (standard_at_two V n e he)
  rw [← mul_smul,← T_add,heq] at hm
  exact hm

end
end MaximalSeshadri.PlaneCech

end


end OAI
