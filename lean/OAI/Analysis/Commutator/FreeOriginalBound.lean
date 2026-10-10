import Mathlib
import OAI.Analysis.Commutator.FreeBaseCompression
import OAI.Analysis.Commutator.NormalFreeCorner

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : VonNeumannAlgebra H)
  (t : FaithfulState A) (htr : ∀ a b : A,t.functional (a*b)=t.functional (b*a))
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (R : Bool → StarSubalgebra ℂ A) (hR : R false=f.range)
  (hfree : Free R t.functional.toLinearMap)
  (hgen : ∀ a : A,t.functional.gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (generatedOperators t R : Set _)))
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D,(factorTrace t f hf).gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

include htr hR hfree hgen hinc hsize hDgen in
theorem normal_free_original_bound
    (hnormal : NormalGNS.BoundedWOTContinuous D (factorTrace t f hf))
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] A) (htrace : ∀ a,τ a=t.functional (j a))
    (hj : ∀ a : B,j a∈R true)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,G (originalEmbedding τ t j htrace x)=originalEmbedding τ t j htrace (T x))
    (hGD : ∀ a : D,G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    (ε β : ℝ) (hε : 0≤ε) (hβ : 0<β) (hβ1 : β≤1)
    (hC : ∀ x,CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t R)
      (TracialGNS.vacuum t.functional) (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*ε := by
  let u : unitary A := ⟨j (s:B),Unitary.map_mem j s.property⟩
  have hu0 : t.functional (u:A)=0 := (htrace (s:B)).symm.trans hs0
  have hu2 : (u:A)*(u:A)=1 := by change j (s:B)*j (s:B)=1; rw [←map_mul,hs2,map_one]
  exact (original_commutator_le_base τ t j htrace R hfree hj G T hGT (s:B)).trans
    (normal_free_corner_bound D t htr f hf R hR hfree hgen I φ inc hinc hsize hDgen
      hnormal hdiffuse G hGD u (hj (s:B)) hu0 hu2 ε β hε hβ hβ1 hC)

end Kadison.FreeBlocks

end

end
end

end OAI
