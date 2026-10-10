import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropPartitionWeights
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixDiagonalComposition
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquareHalfFlip
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCStarInductiveLimit
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorExtension

namespace OAI

noncomputable section


namespace JiangSuConstruction
open Pureness
open scoped CStarAlgebra ComplexOrder TensorProduct

lemma hom_conjugation_difference_bound {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (θ : B →⋆ₐ[ℂ] C) (u : unitary B) (x y : B) :
    ‖(homUnitary θ u:C)*θ x*star (homUnitary θ u:C)-θ y‖≤
      ‖(u:B)*x*star (u:B)-y‖ := by
  change ‖θ (u:B)*θ x*star (θ (u:B))-θ y‖≤_
  rw [←map_star,←map_mul,←map_mul,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le θ _

variable {p q : ℕ} [NeZero p] [NeZero q]
variable {T : Type*} [CStarAlgebra T]
variable (g : DimensionDrop p q ⊗[ℂ] DimensionDrop p q →⋆ₐ[ℂ] T)

theorem tensor_connected_half_flip_of_matching (hg : Function.Injective g)
    (F : Finset (DimensionDrop p q)) {ε : ℝ} (hε : 0<ε)
    (W : C(Interval×Interval,unitary (TensorMat p q))) (hWd : ∀ s,W (s,s)=1)
    (hW : ∀ f∈F,∀ s t,‖unitaryConjugation (W (s,t)) (f.val s)-f.val t‖<ε/42) :
    ∃ u : unitary T,Joined 1 u ∧ ∀ f∈F,
      ‖(u:T)*g (f ⊗ₜ[ℂ] 1)*star (u:T)-g (1 ⊗ₜ[ℂ] f)‖<ε := by
  let θ := faithfulTensorExtension g dimensionDrop_nuclear (squareTensorMap p q p q)
    (squareTensorMap_injective p q p q) (squareTensorMap_dense (p:=p) (q:=q) (r:=p) (s:=q)) hg
  have hθ (z : DimensionDrop p q ⊗[ℂ] DimensionDrop p q) : θ (squareTensorMap p q p q z)=g z :=
    faithfulTensorExtension_apply _ _ _ _ _ _ z
  obtain ⟨u,huj,hu⟩ := square_connected_half_flip_of_matching F hε W hWd hW
  refine ⟨homUnitary θ u,?_,?_⟩
  · simpa only [homUnitary_one] using huj.map (homUnitary_continuous θ)
  · intro f hf
    have hn := hom_conjugation_difference_bound θ u
      (squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)) (squareTensorMap p q p q (1 ⊗ₜ[ℂ] f))
    rw [hθ,hθ] at hn
    exact hn.trans_lt (hu f hf)

end JiangSuConstruction


namespace SequentialCStar.System
open scoped CStarAlgebra

variable {C : ℕ → Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (S : System C)

theorem finite_set_common_stage (F : Finset S.Limit) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (b : F → C n),∀ x : F,‖(x:S.Limit)-S.inclusion n (b x)‖<ε := by
  classical
  choose n a ha using fun x : F => S.finite_stage_approximation (x:S.Limit) hε
  let N := Finset.univ.sup n
  have hN (x : F) : n x≤N := Finset.le_sup (f := n) (Finset.mem_univ x)
  refine ⟨N,fun x => S.map (hN x) (a x),?_⟩
  intro x
  rw [S.inclusion_compatible]
  exact ha x

variable {T : Type*} [CStarAlgebra T]
variable (ι κ : S.Limit →⋆ₐ[ℂ] T)

def ApproximateConjugacy : Prop :=
  ∀ (F : Finset S.Limit) (ε : ℝ),0<ε → ∃ u : unitary T,
    ∀ x∈F,‖(u:T)*ι x*star (u:T)-κ x‖<ε

def FiniteStageConjugacy : Prop :=
  ∀ (n : ℕ) (F : Finset (C n)) (ε : ℝ),0<ε → ∃ u : unitary T,
    ∀ x∈F,‖(u:T)*ι (S.inclusion n x)*star (u:T)-κ (S.inclusion n x)‖<ε

lemma conjugacy_difference_bound (u : unitary T) (x y : S.Limit) :
    ‖(u:T)*ι x*star (u:T)-(u:T)*ι y*star (u:T)‖≤‖x-y‖ := by
  rw [← sub_mul,← mul_sub,←map_sub]
  change ‖((u:T)*ι (x-y))*((star u : unitary T):T)‖≤‖x-y‖
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  exact NonUnitalStarAlgHom.norm_apply_le ι (x-y)

theorem approximateConjugacy_iff_finiteStages :
    ApproximateConjugacy S ι κ ↔ FiniteStageConjugacy S ι κ := by
  classical
  constructor
  · intro h n F ε hε
    obtain ⟨u,hu⟩ := h (F.image (S.inclusion n)) ε hε
    exact ⟨u,fun x hx => hu _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩
  · intro h F ε hε
    obtain ⟨n,b,hb⟩ := S.finite_set_common_stage F (div_pos hε (by norm_num : (0:ℝ)<3))
    obtain ⟨u,hu⟩ := h n (Finset.univ.image b) (ε/3) (by positivity)
    refine ⟨u,?_⟩
    intro x hx
    let z : F := ⟨x,hx⟩
    let y := S.inclusion n (b z)
    have hxy : ‖x-y‖<ε/3 := hb z
    have hmid : ‖(u:T)*ι y*star (u:T)-κ y‖<ε/3 :=
      hu _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)
    have hleft : ‖(u:T)*ι x*star (u:T)-(u:T)*ι y*star (u:T)‖<ε/3 :=
      (S.conjugacy_difference_bound ι u x y).trans_lt hxy
    have hright : ‖κ y-κ x‖<ε/3 := by
      rw [←map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le κ (y-x)).trans_lt (by simpa only [norm_sub_rev] using hxy)
    have htri₁ := norm_sub_le_norm_sub_add_norm_sub
      ((u:T)*ι x*star (u:T)) ((u:T)*ι y*star (u:T)) (κ x)
    have htri₂ := norm_sub_le_norm_sub_add_norm_sub
      ((u:T)*ι y*star (u:T)) (κ y) (κ x)
    linarith

end SequentialCStar.System

end

end OAI
