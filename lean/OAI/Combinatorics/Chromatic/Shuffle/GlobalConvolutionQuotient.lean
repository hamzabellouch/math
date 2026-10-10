import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalShuffleCoalgebra

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convVanishes_zeroMap (n : ℕ) :
    convVanishes a c η hc θ n (0 : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) := by
  intro k hk x
  rfl

lemma convVanishes_add {n : ℕ}
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ n g) :
    convVanishes a c η hc θ n (f+g) := by
  intro k hk x
  change f.ofConv _+g.ofConv _=0
  rw [hf k hk x,hg k hk x,add_zero]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_neg {n : ℕ}
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) : convVanishes a c η hc θ n (-f) := by
  intro k hk x
  change -(f.ofConv _)=0
  rw [hf k hk x,neg_zero]

noncomputable def convolutionIdeal (n : ℕ) :
    TwoSidedIdeal (WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :=
  TwoSidedIdeal.mk' {f | convVanishes a c η hc θ n f}
    (convVanishes_zeroMap a c η hc θ n)
    (convVanishes_add a c η hc θ) (convVanishes_neg a c η hc θ)
    (fun {f g} hg=>by
      change convVanishes a c η hc θ n (f*g)
      simpa only [zero_add] using convVanishes_mul a c η hc θ
        (convVanishes_zero a c η hc θ f) hg)
    (fun {f g} hf=>by
      change convVanishes a c η hc θ n (f*g)
      simpa only [add_zero] using convVanishes_mul a c η hc θ hf
        (convVanishes_zero a c η hc θ g))

abbrev ConvolutionQuotient (n : ℕ) := (convolutionIdeal a c η hc θ (A := A) n).ringCon.Quotient

noncomputable def convolutionProjection (n : ℕ) :
    WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A) →ₐ[ℚ] ConvolutionQuotient a c η hc θ (A := A) n :=
  (convolutionIdeal a c η hc θ n).ringCon.mkₐ ℚ

lemma convolutionProjection_eq_zero_iff (n : ℕ)
    (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convolutionProjection a c η hc θ n f=0 ↔ convVanishes a c η hc θ n f := by
  have h := (convolutionIdeal a c η hc θ (A := A) n).ringCon.eq (a := f) (b := 0)
  change convolutionProjection a c η hc θ n f=0 ↔ _ at h
  apply h.trans
  rw [←TwoSidedIdeal.mem_iff]
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

lemma convolutionProjection_eq_iff (n : ℕ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convolutionProjection a c η hc θ n f=convolutionProjection a c η hc θ n g ↔
      ∀ k : SlopeWeight c η hc θ, dimensionSize k.1.val < n →
        ∀ x : unitalComponent a c η hc θ k,
          f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
            g.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) := by
  rw [←sub_eq_zero,←map_sub,convolutionProjection_eq_zero_iff]
  simp only [convVanishes,WithConv.ofConv_sub,LinearMap.sub_apply,sub_eq_zero]

lemma convolutionProjection_nilpotent (n : ℕ)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) :
    (convolutionProjection a c η hc θ n f)^n=0 := by
  rw [←map_pow,convolutionProjection_eq_zero_iff]
  exact convVanishes_pow a c η hc θ hf n

end ElementaryPositivity.RawShuffle

end

end OAI
