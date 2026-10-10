import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CechH0
import OAI.AlgebraicGeometry.Seshadri.Cohomology.KernelH1
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricVertexPresentation

namespace OAI


                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

theorem toric_H0_finite (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  classical
  obtain ⟨n,e,hv,hs⟩ := toric_free_presentation V stable g hg hgen clear
  let N := (freeMap (K := K) e).ker
  let := free_H0_finite (K := K) (Σ i, ι i) (-(n : ℤ))
  let f := (freeMap (K := K) e).restrictScalars K
  let NA := (freeA (K := K) (Σ i, ι i)).comap f.ker.subtype
  let NB := (freeB (K := K) (Σ i, ι i)).comap f.ker.subtype
  let NC := (freeC (K := K) (Σ i, ι i) (-(n : ℤ))).comap f.ker.subtype
  let : AddCommGroup (cycles NA NB NC) := by
    let group := Submodule.addCommGroup (R := K) (M := NA × NB × NC) (cycles NA NB NC)
    exact group
  let : Module K (cycles NA NB NC) := by
    let moduleStructure := Submodule.module (R := K) (M := NA × NB × NC) (cycles NA NB NC)
    exact moduleStructure
  let : Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles NA NB NC))
      (fullBoundaries NA NB NC)) :=
    kernel_H1_finite N (-(n : ℤ))
  apply finite_H0_of_presentation f
    (freeA _) (freeB _) (freeC _ (-(n : ℤ))) V
  · intro x hx
    exact hv 0 x (by rwa [freeVertex_zero])
  · intro x hx
    exact hv 1 x (by rwa [freeVertex_one])
  · intro x hx
    exact hv 2 x (by rwa [freeVertex_two])
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 0 x hx
    exact ⟨y,by rwa [freeVertex_zero] at hy,he⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 1 x hx
    exact ⟨y,by rwa [freeVertex_one] at hy,he⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 2 x hx
    exact ⟨y,by rwa [freeVertex_two] at hy,he⟩
end
end MaximalSeshadri.PlaneCech

end

end OAI
