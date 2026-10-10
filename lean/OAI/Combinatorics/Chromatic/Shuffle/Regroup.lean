import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Interaction
import OAI.Combinatorics.Chromatic.Shuffle.DimensionEquivS

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

inductive Regroup : SplitTree I → SplitTree I → Type u
  | refl (T) : Regroup T T
  | assoc (T U V) : Regroup (.node (.node T U) V) (.node T (.node U V))
  | swap (T U) : Regroup (.node T U) (.node U T)
  | node {T U V W} : Regroup T U → Regroup V W → Regroup (.node T V) (.node U W)
  | trans {T U V} : Regroup T U → Regroup U V → Regroup T V

namespace Regroup
noncomputable def vars {T U : SplitTree I} : Regroup T U → T.Vars ≃ U.Vars
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.sumAssoc _ _ _
  | .swap _ _ => Equiv.sumComm _ _
  | .node f g => Equiv.sumCongr f.vars g.vars
  | .trans f g => f.vars.trans g.vars

omit [Fintype I] [DecidableEq I] in
lemma pack {T U : SplitTree I} (e : Regroup T U) (x : T.Vars) :
    U.packIndex (e.vars x)=T.packIndex x := by
  induction e with
  | refl T => rfl
  | assoc T U V => rcases x with (x|x)|x <;> rfl
  | swap T U => cases x <;> rfl
  | node f g ihf ihg => cases x with
    | inl x => exact ihf x
    | inr x => exact ihg x
  | trans f g ihf ihg => exact (ihg (f.vars x)).trans (ihf x)

omit [Fintype I] [DecidableEq I] in
lemma dimension {T U : SplitTree I} (e : Regroup T U) : T.dim=U.dim := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact add_assoc _ _ _
  | swap T U => exact add_comm _ _
  | node f g ihf ihg => exact congrArg₂ (·+·) ihf ihg
  | trans f g ihf ihg => exact ihf.trans ihg

noncomputable def equivalence (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    {T U : SplitTree I} : Regroup T U → tensor A T ≃ₐ[ℚ] tensor A U
  | .refl _ => AlgEquiv.refl
  | .assoc T U V => Algebra.TensorProduct.assoc ℚ ℚ ℚ (tensor A T) (tensor A U) (tensor A V)
  | .swap T U => Algebra.TensorProduct.comm ℚ (tensor A T) (tensor A U)
  | .node f g => Algebra.TensorProduct.congr (f.equivalence A) (g.equivalence A)
  | .trans f g => (f.equivalence A).trans (g.equivalence A)

omit [Fintype I] [DecidableEq I] in
lemma tensorMap_natural (A C : (I → ℕ) → CommAlgCat.{u} ℚ) (f : ∀ d,A d →ₐ[ℚ] C d)
    {T U : SplitTree I} (e : Regroup T U) (x : tensor A T) :
    e.equivalence C (tensorMap A C f T x)=tensorMap A C f U (e.equivalence A x) := by
  induction e with
  | refl T => rfl
  | assoc T U V =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y => rfl
  | swap T U =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y => rfl
  | node e g ihe ihg =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change e.equivalence C (tensorMap A C f _ x) ⊗ₜ[ℚ]
          g.equivalence C (tensorMap A C f _ y)=
        tensorMap A C f _ (e.equivalence A x) ⊗ₜ[ℚ]
          tensorMap A C f _ (g.equivalence A y)
      rw [ihe,ihg]
  | trans e g ihe ihg =>
    change g.equivalence C (e.equivalence C (tensorMap A C f _ x))=_
    rw [ihe,ihg]
    rfl

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_natural {T U : SplitTree I} (e : Regroup T U) (x : tensor rawFamily T) :
    tensorValue U (e.equivalence rawFamily x)=rename e.vars (tensorValue T x) := by
  induction e with
  | refl T =>
    change tensorValue T x=rename id (tensorValue T x)
    simp only [rename_id,AlgHom.id_apply]
  | assoc T U V =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y =>
        change tensorValue (.node T (.node U V)) (x ⊗ₜ[ℚ] (y ⊗ₜ[ℚ] z)) = _
        rw [tensorValue_tmul T (.node U V),tensorValue_tmul U V,
          tensorValue_tmul (.node T U) V,tensorValue_tmul T U]
        simp only [map_mul,rename_rename]
        exact (mul_assoc _ _ _).symm
  | swap T U =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change tensorValue (.node U T) (y ⊗ₜ[ℚ] x)=_
      rw [tensorValue_tmul U T,tensorValue_tmul T U]
      simp only [map_mul,rename_rename]
      exact mul_comm _ _
  | node e g ihe ihg =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change tensorValue (.node _ _) (e.equivalence rawFamily x ⊗ₜ[ℚ] g.equivalence rawFamily y)=_
      rw [tensorValue_tmul,ihe,ihg,tensorValue_tmul,map_mul,rename_rename,rename_rename,rename_rename,rename_rename]
      rfl
  | trans e g ihe ihg =>
    change tensorValue _ (g.equivalence rawFamily (e.equivalence rawFamily x))=_
    rw [ihg,ihe,rename_rename]
    rfl

lemma rawRestriction_natural {T U : SplitTree I} (e : Regroup T U) (f : S T.dim) :
    e.equivalence rawFamily (rawRestriction T f)=
      rawRestriction U (dimensionEquivS e.dimension f) := by
  apply tensorValue_injective U
  rw [tensorValue_natural]
  exact rawRestriction_regroup_of_pack_preserving e.dimension e.vars e.pack f

lemma dimensionEquivB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) (f : S d) :
    dimensionEquivB a μ h (quotientAlg a μ d f)=
      quotientAlg a μ e (dimensionEquivS h f) := by
  subst e
  rfl

lemma restrictionB_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionB a c η hc θ T hT f)=
      restrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionB a c η hc θ T hT (quotientAlg a _ T.dim f))=
      restrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension (quotientAlg a _ T.dim f))
    rw [dimensionEquivB_mk,restrictionB_mk,restrictionB_mk]
    change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
      (tensorMap rawFamily (quotientFamily a (SlopeArithmetic.slope c η))
        (quotientAlg a (SlopeArithmetic.slope c η)) T (rawRestriction T f))=_
    erw [tensorMap_natural]
    rw [rawRestriction_natural]
    rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
