import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FreeVertices

namespace OAI


                                        
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

abbrev kernelVertex (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) (i : Fin 3) :
    Submodule K N := (freeVertex ι d i).comap (N.subtype.restrictScalars K)

omit [Fintype ι] in
lemma kernelVertex_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ)
    (i : Fin 3) (z : ℤ × ℤ) (hz : z ∈ vertexCone i) (x : N) (hx : x ∈ kernelVertex N d i) :
    T (K := K) z • x ∈ kernelVertex N d i := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeVertex ι d i
  exact freeVertex_stable d i z hz (x : ι → LaurentPlane.Ring K) hx

lemma kernelVertex_finite (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) (i : Fin 3) :
    letI := vertexModule (K := K) (M := N) i
    Module.Finite (MvPolynomial (Fin 3) K)
      (vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)) := by
  let := vertexModule (K := K) (M := N) i
  let := vertexModule (K := K) (M := ι → LaurentPlane.Ring K) i
  let W := vertexSubmodule i (freeVertex (K := K) ι d i) (freeVertex_stable d i)
  let Q := vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)
  let : Module.Finite (MvPolynomial (Fin 3) K) W := freeVertex_finite d i
  let f : Q →ₗ[MvPolynomial (Fin 3) K] W :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective f
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun t : W => (t : ι → LaurentPlane.Ring K)) h))

lemma kernelVertex_generators (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) (i : Fin 3) :
    ∃ n : ℕ, ∃ g : Fin n → N, (∀ a, g a ∈ kernelVertex N d i) ∧
      kernelVertex N d i = monomialSpan (K := K) (vertexCone i) g := by
  let := vertexModule (K := K) (M := N) i
  let := vertexModule_tower (K := K) (M := N) i
  let Q := vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)
  let : Module.Finite (MvPolynomial (Fin 3) K) Q := kernelVertex_finite N d i
  let F : Q →ₗ[K] N := Q.subtype.restrictScalars K
  have he : F.range = kernelVertex N d i := by
    ext x
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  obtain ⟨n,g,hg,hgen⟩ := finite_monomial_generators i id F
    (by rw [he]; exact kernelVertex_stable N d i)
    (by intro j x; change vertexPolynomial (K := K) i (MvPolynomial.X j) • (x : N) = _; rw [vertexPolynomial_X]; rfl)
  exact ⟨n,g,by rwa [he] at hg,by rwa [he] at hgen⟩

end
end MaximalSeshadri.PlaneCech

end

end OAI
