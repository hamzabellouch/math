import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerMaps

namespace OAI

section

noncomputable section
namespace CStarAbsorption
open Pureness NormUltra NormUltra.QuotientAlgebra
open scoped CStarAlgebra ENNReal TensorProduct

variable {A D B : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
variable (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B) (κ : D →⋆ₐ[ℂ] B)
    (hic : ∀ a d,Commute (ι a) (κ d))
    (φ : D →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => A) U)
    (hφ : ∀ a d,Commute (diagonalHom U a) (φ d))

 def preimageTensor : A ⊗[ℂ] D →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => A) U :=
  commutingStarTensorHom (diagonalHom U) φ hφ

 theorem finite_tensor_control (z : A ⊗[ℂ] D) :
    ∃ F : Finset D,∃ C : ℝ,0≤C ∧
      ∀ u : unitary (QuotientAlgebra (fun _ : ℕ => B) U),
      (∀ a,Commute (u : QuotientAlgebra (fun _ : ℕ => B) U) (diagonalHom U (ι a))) →
      ∀ ε : ℝ,0≤ε →
      (∀ d∈F,‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (φ d)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (κ d)‖≤ε) →
      ‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (preimageTensor U φ hφ z)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (commutingStarTensorHom ι κ hic z)‖≤C*ε := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul a d =>
    refine ⟨{d},‖a‖,norm_nonneg _,?_⟩
    intro u hu ε hε hf
    have hd := hf d (Finset.mem_singleton_self _)
    have hcomm := (hu a).eq
    have hb : ‖diagonalHom U (ι a)‖≤‖a‖ :=
      (NonUnitalStarAlgHom.norm_apply_le (diagonalHom U) (ι a)).trans
        (NonUnitalStarAlgHom.norm_apply_le ι a)
    change ‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι
      (diagonalHom U a*φ d)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (ι a*κ d)‖≤‖a‖*ε
    rw [map_mul,map_diagonalHom,map_mul]
    have he : (u : QuotientAlgebra (fun _ : ℕ => B) U)*(diagonalHom U (ι a)*QuotientAlgebra.map U ι (φ d))*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (ι a)*diagonalHom U (κ d)=
        diagonalHom U (ι a)*((u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (φ d)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (κ d)) := by
      rw [mul_sub,←mul_assoc (u : QuotientAlgebra (fun _ : ℕ => B) U) (diagonalHom U (ι a)),hcomm]
      simp only [mul_assoc]
    rw [he]
    exact (norm_mul_le _ _).trans
      (mul_le_mul hb hd (norm_nonneg _) (norm_nonneg _))
  | add z w hz hw =>
    obtain ⟨F,C,hC,hz⟩ := hz
    obtain ⟨G,K,hK,hw⟩ := hw
    refine ⟨F∪G,C+K,add_nonneg hC hK,?_⟩
    intro u hu ε hε hf
    have hz' := hz u hu ε hε (fun d hd => hf d (Finset.mem_union_left _ hd))
    have hw' := hw u hu ε hε (fun d hd => hf d (Finset.mem_union_right _ hd))
    simp only [map_add]
    have he : (u : QuotientAlgebra (fun _ : ℕ => B) U)*
        (QuotientAlgebra.map U ι (preimageTensor U φ hφ z)+QuotientAlgebra.map U ι (preimageTensor U φ hφ w))*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-
        (diagonalHom U (commutingStarTensorHom ι κ hic z)+diagonalHom U (commutingStarTensorHom ι κ hic w))=
        ((u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (preimageTensor U φ hφ z)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (commutingStarTensorHom ι κ hic z))+
        ((u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (preimageTensor U φ hφ w)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (commutingStarTensorHom ι κ hic w)) := by noncomm_ring
    rw [he,add_mul]
    exact (norm_add_le _ _).trans (add_le_add hz' hw')

end CStarAbsorption

end
end

end OAI
