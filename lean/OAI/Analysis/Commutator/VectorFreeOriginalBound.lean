import Mathlib
import OAI.Analysis.Commutator.FreeOriginalBound
import OAI.Analysis.Commutator.RepresentedCornerBound
import OAI.Analysis.Commutator.VectorStageGeneration

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeMoments FreeBlocks

variable {H B : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M) (hR : R false=(inclusion M D hDM).range)
  (hfree : Free R (subalgebraTrace M ξ).toLinearMap)
  (hgen : ∀ a : M,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
    (((iSup R).map M.toStarSubalgebra.subtype) : Set (H →L[ℂ] H))))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : GeneratedByStages D ξ I φ)

include htr hR hfree hgen hinc hsize hDgen in
theorem free_original_bound
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] M) (htrace : ∀ a,τ a=subalgebraTrace M ξ (j a))
    (hj : ∀ a : B,j a∈R true)
    (U : H →L[ℂ] H) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,subalgebraCompression M ξ U
      (originalEmbedding τ (vectorState M ξ hfaith hone) j htrace x)=
      originalEmbedding τ (vectorState M ξ hfaith hone) j htrace (T x))
    (hGD : ∀ d : D,U*(d:H →L[ℂ] H)=(d:H →L[ℂ] H)*U)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    {c β : ℝ} (hc : 0≤c) (hβ : 0<β) (hβ1 : β≤1)
    (hC : CornerCommutatorBound M ξ hfaith hone (inclusion M D hDM) R U c (β:ℂ)) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c :=
  normal_free_original_bound D (vectorState M ξ hfaith hone) htr
    (inclusion M D hDM) (inclusion_injective M D hDM) R hR hfree
    (gns_generation M ξ hfaith hone R hgen) I φ inc hinc hsize
    (factorTrace_generated D ξ I φ M hfaith hone hDM hDgen)
    (factorTrace_inclusion_normal M ξ hfaith hone D hDM) hdiffuse
    τ j htrace hj (subalgebraCompression M ξ U) T hGT (fun d => commutes M ξ U (inclusion M D hDM d) (hGD d)) s hs0 hs2 c β hc hβ hβ1 hC

include htr hR hfree hgen hinc hsize hDgen in
theorem free_original_bound_represented
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] M) (htrace : ∀ a,τ a=subalgebraTrace M ξ (j a))
    (hj : ∀ a : B,j a∈R true)
    (U : H →L[ℂ] H) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,subalgebraCompression M ξ U
      (originalEmbedding τ (vectorState M ξ hfaith hone) j htrace x)=
      originalEmbedding τ (vectorState M ξ hfaith hone) j htrace (T x))
    (hGD : ∀ d : D,U*(d:H →L[ℂ] H)=(d:H →L[ℂ] H)*U)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    {c β : ℝ} (hc : 0≤c) (hβ : 0<β) (hβ1 : β≤1)
    (hC : RepresentedCornerBound M ξ D U c (β:ℂ)) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c :=
  free_original_bound M ξ htr hfaith hone D hDM R hR hfree hgen I φ inc hinc
    hsize hDgen hdiffuse τ j htrace hj U T hGT hGD s hs0 hs2 hc hβ hβ1
    (represented_corner_bound M ξ htr hfaith hone D hDM R U c (β:ℂ) hC)

end Kadison.VectorGNS

end

end
end

end OAI
