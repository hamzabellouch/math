import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule
import OAI.AlgebraicGeometry.Seshadri.Cohomology.KernelVertices
import OAI.AlgebraicGeometry.Seshadri.Geometry.FreeVertexClearing

namespace OAI


                                  
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K] {ι : Type*}

abbrev kernelA (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) : Submodule K N :=
  (freeA ι).comap (N.subtype.restrictScalars K)
abbrev kernelB (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) : Submodule K N :=
  (freeB ι).comap (N.subtype.restrictScalars K)
abbrev kernelC (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) : Submodule K N :=
  (freeC ι d).comap (N.subtype.restrictScalars K)

lemma kernelA_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K))
    (z : ℤ × ℤ) (hz : z ∈ coneA) (x : N) (hx : x ∈ kernelA N) :
    T (K := K) z • x ∈ kernelA N := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeA ι
  exact freeA_stable z hz (x : ι → LaurentPlane.Ring K) hx
lemma kernelB_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K))
    (z : ℤ × ℤ) (hz : z ∈ coneB) (x : N) (hx : x ∈ kernelB N) :
    T (K := K) z • x ∈ kernelB N := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeB ι
  exact freeB_stable z hz (x : ι → LaurentPlane.Ring K) hx
lemma kernelC_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ)
    (z : ℤ × ℤ) (hz : z ∈ coneC 0) (x : N) (hx : x ∈ kernelC N d) :
    T (K := K) z • x ∈ kernelC N d := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeC ι d
  exact freeC_stable d z hz (x : ι → LaurentPlane.Ring K) hx

lemma kernelVertex_zero (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 0 = kernelA N ⊓ kernelB N := by
  simp only [kernelVertex,freeVertex_zero,Submodule.comap_inf]
lemma kernelVertex_one (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 1 = kernelA N ⊓ kernelC N d := by
  simp only [kernelVertex,freeVertex_one,Submodule.comap_inf]
lemma kernelVertex_two (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 2 = kernelB N ⊓ kernelC N d := by
  simp only [kernelVertex,freeVertex_two,Submodule.comap_inf]

lemma kernel_boundaries (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    vertexBoundaries (kernelA N) (kernelB N) (kernelC N d) (kernelVertex N d) =
      fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d) := by
  simp only [vertexBoundaries,boundaries,kernelVertex_zero,kernelVertex_one,kernelVertex_two,
    Submodule.comap_subtype_self,Submodule.map_top,fullBoundaries]

local instance kernelCyclesAddCommGroup
    (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    AddCommGroup (cycles (kernelA N) (kernelB N) (kernelC N d)) := by
  let group := Submodule.addCommGroup (R := K)
    (M := (kernelA N) × (kernelB N) × (kernelC N d))
    (cycles (kernelA N) (kernelB N) (kernelC N d))
  exact group

local instance kernelCyclesModule
    (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module K (cycles (kernelA N) (kernelB N) (kernelC N d)) := by
  let moduleStructure := Submodule.module (R := K)
    (M := (kernelA N) × (kernelB N) × (kernelC N d))
    (cycles (kernelA N) (kernelB N) (kernelC N d))
  exact moduleStructure

local instance kernelCyclesHasQuotient
    (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    HasQuotient (cycles (kernelA N) (kernelB N) (kernelC N d))
      (Submodule K (cycles (kernelA N) (kernelB N) (kernelC N d))) :=
  Submodule.hasQuotient (R := K) (M := cycles (kernelA N) (kernelB N) (kernelC N d))

variable [Fintype ι]

theorem kernel_H1_finite (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module.Finite K ((cycles (K := K) (kernelA N) (kernelB N) (kernelC N d)) ⧸
      fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d)) := by
  choose n g hg hgen using kernelVertex_generators N d
  have incA : kernelVertex N d 0 ≤ kernelA N := by rw [kernelVertex_zero]; exact inf_le_left
  have incB : kernelVertex N d 0 ≤ kernelB N := by rw [kernelVertex_zero]; exact inf_le_right
  have incC : kernelVertex N d 1 ≤ kernelC N d := by rw [kernelVertex_one]; exact inf_le_right
  rw [← kernel_boundaries N d]
  apply toric_H1_finite (kernelVertex N d) (kernelVertex_stable N d) g hg
  · intro i j x hx
    exact freeVertex_cross_clearing d i j (x : ι → LaurentPlane.Ring K) hx
  · exact kernelA_stable N
  · exact kernelB_stable N
  · exact kernelC_stable N d
  · exact incA
  · exact incB
  · exact incC
  · apply localized_span (vertexCone 0) coneA (g 0) (kernelA N) (fun a => incA (hg 0 a))
      (kernelA_stable N)
    intro x hx
    obtain ⟨q,hq⟩ := freeA_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 1-weight 0),?_,?_⟩
    · rw [← hgen 0]; exact hq
    · intro w hw
      simp [vertexCone,coneA,weight] at hw ⊢
      exact hw.1
  · apply localized_span (vertexCone 0) coneB (g 0) (kernelB N) (fun a => incB (hg 0 a))
      (kernelB_stable N)
    intro x hx
    obtain ⟨q,hq⟩ := freeB_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 2-weight 0),?_,?_⟩
    · rw [← hgen 0]; exact hq
    · intro w hw
      simp [vertexCone,coneB,weight] at hw ⊢
      exact hw.2
  · apply localized_span (vertexCone 1) (coneC 0) (g 1) (kernelC N d) (fun a => incC (hg 1 a))
      (kernelC_stable N d)
    intro x hx
    obtain ⟨q,hq⟩ := freeC_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 2-weight 1),?_,?_⟩
    · rw [← hgen 1]; exact hq
    · intro w hw
      simp [vertexCone,coneC,weight] at hw ⊢
      omega
end
end MaximalSeshadri.PlaneCech

end

end OAI
