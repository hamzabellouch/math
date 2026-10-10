import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalConvolutionSeries

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

lemma signedLeftRight_convolution :
    toConv (signedLeft a c η hc θ) * toConv (signedRight a c η hc θ)=
      toConv (globalCoproductAlgHom a c η hc θ).toLinearMap := by
  apply ofConv_injective
  apply LinearMap.ext
  intro x
  rw [LinearMap.convMul_apply]
  exact signedLeftRight_product a c η hc θ (globalCoproduct a c η hc θ x)

lemma signedRightLeft_convolution :
    toConv (signedRight a c η hc θ) * toConv (signedLeft a c η hc θ)=
      toConv (globalCoproductAlgHom a c η hc θ).toLinearMap := by
  apply ofConv_injective
  apply LinearMap.ext
  intro x
  rw [LinearMap.convMul_apply]
  exact (signedRightLeft_product a c η hc θ (globalCoproduct a c η hc θ x)).trans
    (globalCoproduct_cocommutative a c η hc θ hχ.out x)

lemma convPost_id {A : Type*} [Ring A] [Algebra ℚ A]
    (φ : UnitalShuffle a c η hc θ →ₐ[ℚ] A) :
    convPost φ (toConv LinearMap.id)=toConv φ.toLinearMap := rfl

lemma convPost_J {A : Type*} [Ring A] [Algebra ℚ A]
    (φ : UnitalShuffle a c η hc θ →ₐ[ℚ] A) :
    convPost φ (convolutionJ a c η hc θ)=toConv φ.toLinearMap-1 := by
  rw [convolutionJ,map_sub,convPost_id,map_one]

lemma convVanishes_post {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) {n : ℕ} {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) : convVanishes a c η hc θ n (convPost φ f) := by
  intro k hk x
  rw [convPost_apply,hf k hk x,map_zero]

lemma signedConvolution_J_product :
    (1+convPost (signedLeftAlgHom a c η hc θ) (convolutionJ a c η hc θ))*
      (1+convPost (signedRightAlgHom a c η hc θ) (convolutionJ a c η hc θ))-1=
      convPost (globalCoproductAlgHom a c η hc θ) (convolutionJ a c η hc θ) := by
  simp only [convPost_J]
  have h (z : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ)) : 1+(z-1)=z := by abel
  rw [h,h]
  exact congrArg (fun x=>x-1) (signedLeftRight_convolution a c η hc θ)

lemma signedConvolution_J_commute :
    Commute (convPost (signedLeftAlgHom a c η hc θ) (convolutionJ a c η hc θ))
      (convPost (signedRightAlgHom a c η hc θ) (convolutionJ a c η hc θ)) := by
  have h : Commute (toConv (signedLeft a c η hc θ)) (toConv (signedRight a c η hc θ)) :=
    (signedLeftRight_convolution a c η hc θ).trans (signedRightLeft_convolution a c η hc θ).symm
  simp only [convPost_J]
  exact (h.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)

noncomputable def globalPrimitiveLog : UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv

theorem globalPrimitiveLog_primitive (x : UnitalShuffle a c η hc θ) :
    globalCoproduct a c η hc θ (globalPrimitiveLog a c η hc θ x)=
      globalPrimitiveLog a c η hc θ x⊗ₜ[ℚ]globalUnit a c η hc θ+
        globalUnit a c η hc θ⊗ₜ[ℚ]globalPrimitiveLog a c η hc θ x := by
  have h := convSeries_log_product a c η hc θ (signedConvolution_J_commute a c η hc θ)
    (convVanishes_post a c η hc θ (signedLeftAlgHom a c η hc θ)
      (convolutionJ_vanishes a c η hc θ))
    (convVanishes_post a c η hc θ (signedRightAlgHom a c η hc θ)
      (convolutionJ_vanishes a c η hc θ))
  rw [signedConvolution_J_product,←convSeries_post,←convSeries_post,←convSeries_post] at h
  exact congrArg (fun f=>f.ofConv x) h

end ElementaryPositivity.RawShuffle

end

end OAI
