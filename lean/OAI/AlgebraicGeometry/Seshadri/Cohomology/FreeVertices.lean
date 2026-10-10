import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricH1
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricPolynomial

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

def twistCone (d : ℤ) (i : Fin 3) : Set (ℤ × ℤ) :=
  {z | z - d • weight i ∈ vertexCone i}
def freeVertex (ι : Type*) (d : ℤ) (i : Fin 3) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported (twistCone d i))

lemma freeVertex_zero (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 0 = freeA ι ⊓ freeB ι := by
  have he : twistCone d 0 = coneA ∩ coneB := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneB]
  ext m
  simp only [freeVertex,freeA,freeB,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_one (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 1 = freeA ι ⊓ freeC ι d := by
  have he : twistCone d 1 = coneA ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneC]
    omega
  ext m
  simp only [freeVertex,freeA,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_two (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 2 = freeB ι ⊓ freeC ι d := by
  have he : twistCone d 2 = coneB ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneB,coneC]
    omega
  ext m
  simp only [freeVertex,freeB,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop

lemma freeVertex_stable {ι : Type*} (d : ℤ) (i : Fin 3) (z : ℤ × ℤ) (hz : z ∈ vertexCone i)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeVertex ι d i) :
    T (K := K) z • m ∈ freeVertex ι d i := by
  intro a ha
  apply supported_monomial_mul (twistCone d i) (twistCone d i) z _ (m a) (hm a ha)
  intro w hw
  change z+w-d • weight i ∈ vertexCone i
  rw [add_sub_assoc]
  exact vertexCone_add i hz hw

lemma freeVertex_monomial_generators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℤ) (i : Fin 3) :
    freeVertex (K := K) ι d i = monomialSpan (K := K) (vertexCone i)
      (fun a : ι => Pi.single a (T (d • weight i))) := by
  let g : ι → (ι → LaurentPlane.Ring K) := fun a => Pi.single a (T (d • weight i))
  have singleton (a : ι) (z : ℤ × ℤ) : T (K := K) z • g a = Pi.single a (T (z+d • weight i)) := by
    ext b
    by_cases hb : b=a
    · subst b
      simp only [Pi.smul_apply,g,Pi.single_eq_same,smul_eq_mul,← T_add]
    · simp [g,Pi.single_eq_of_ne hb]
  apply le_antisymm
  · intro m hm
    let V := monomialSpan (K := K) (vertexCone i) g
    have hc (a : ι) : (m a) • ((Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K)) ∈ V := by
      apply smul_supported_mem V (twistCone d i) _ _ (m a) (hm a (Set.mem_univ a))
      intro z hz
      have hh : T (K := K) (z-d • weight i) • g a = T (K := K) z • (Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K) := by
        rw [singleton,sub_add_cancel]
        ext b
        by_cases hb : b=a
        · subst b; simp
        · simp [Pi.single_eq_of_ne hb]
      rw [← hh]
      exact Submodule.subset_span ⟨a,z-d • weight i,hz,rfl⟩
    have he : ∑ a, (m a) • (Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K) = m := by
      ext b
      simp [Pi.single_apply]
    rw [← he]
    exact V.sum_mem (fun a _ => hc a)
  · apply monomialSpan_le
    · intro a
      apply single_monomial_mem
      change d • weight i - d • weight i ∈ vertexCone i
      simpa using direction_mem i i 0
    · exact freeVertex_stable d i

lemma freeVertex_finite {ι : Type*} [Fintype ι] (d : ℤ) (i : Fin 3) :
    letI := vertexModule (K := K) (M := ι → LaurentPlane.Ring K) i
    Module.Finite (MvPolynomial (Fin 3) K)
      (vertexSubmodule i (freeVertex (K := K) ι d i) (freeVertex_stable d i)) := by
  classical
  apply vertexSubmodule_finite i (freeVertex ι d i) (freeVertex_stable d i)
    (fun index : ι => Pi.single index (T (d • weight i)))
  · intro a
    apply single_monomial_mem
    change d • weight i - d • weight i ∈ vertexCone i
    simpa using direction_mem i i 0
  · exact freeVertex_monomial_generators d i

end
end MaximalSeshadri.PlaneCech

end


end OAI
