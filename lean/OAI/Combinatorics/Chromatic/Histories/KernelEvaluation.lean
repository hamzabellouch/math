import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PointEvaluation
import OAI.Combinatorics.Chromatic.Shuffle.LaurentKernel

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

noncomputable def leafVarsEquiv : (T : SplitTree I) →
    T.Vars ≃ (Σ z : T.Centers, Σ i, Fin (T.leafDimension z i))
  | .leaf d =>
    { toFun := fun x=>⟨(),x⟩
      invFun := fun x=>x.2
      left_inv := fun _=>rfl
      right_inv := fun ⟨z,x⟩=>by cases z; rfl }
  | .node l r =>
    (Equiv.sumCongr (leafVarsEquiv l) (leafVarsEquiv r)).trans
      (Equiv.sumSigmaDistrib (fun z : (SplitTree.node l r).Centers=>Σ i,Fin ((SplitTree.node l r).leafDimension z i))).symm

omit [Fintype I] [DecidableEq I] in
@[simp] lemma leafVarsEquiv_center (T : SplitTree I) (x : T.Vars) :
    (T.leafVarsEquiv x).1=T.centerOfVar x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr => cases x with
    | inl x => exact congrArg Sum.inl (hl x)
    | inr x => exact congrArg Sum.inr (hr x)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma leafVarsEquiv_pack (T : SplitTree I) (x : T.Vars) :
    (T.leafVarsEquiv x).2.1=T.packIndex x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr => cases x with
    | inl x => exact hl x
    | inr x => exact hr x

noncomputable def pointedTensorRestriction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim →ₐ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R) :=
  Algebra.TensorProduct.map (pointedRestrictionB a c η hc θ L hL v)
    (pointedRestrictionB a c η hc θ R hR w)

noncomputable def crossPointEval (L R : SplitTree I) (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    MvPolynomial (CellVars L.dim R.dim) ℚ →+* ℚ :=
  eval (Sum.elim (v ∘ L.centerOfVar ∘ L.varEquiv.symm)
    (w ∘ R.centerOfVar ∘ R.varEquiv.symm))

lemma pointedTensorRestriction_quotient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (x : S L.dim ⊗[ℚ] S R.dim) :
    pointedTensorRestriction a c η hc θ L R hL hR v w
      (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
        (quotientAlg a (SlopeArithmetic.slope c η) R.dim) x)=
      algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))
        (crossPointEval L R v w (RawShuffle.tensorValue L.dim R.dim x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [pointedTensorRestriction,Algebra.TensorProduct.map_tmul,pointedRestrictionB_mk,
      RawShuffle.tensorValue_tmul,crossPointEval,map_mul,eval_rename]
    simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    simp only [Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,
      TensorProduct.tmul_smul,smul_smul,Algebra.TensorProduct.one_def,mul_comm,
      mul_smul_comm,smul_smul,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,hx,hy]
end SplitTree
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity SplitTree
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma pointed_quotientInverseKernel (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
      (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val =
    mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (mapRing (crossPointEval L R v w) (rawInverseKernelUnit a L.dim R.dim).val) := by
  apply HahnSeries.ext
  funext k
  change pointedTensorRestriction a c η hc θ L R hL hR v w
    (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
      (quotientAlg a (SlopeArithmetic.slope c η) R.dim) ((inverseKernelUnit a L.dim R.dim).val.coeff k))=_
  rw [pointedTensorRestriction_quotient]
  have h:=congrArg (fun f : LaurentSeries (MvPolynomial (CellVars L.dim R.dim) ℚ)=>f.coeff k)
    (realize_inverseKernelUnit a L.dim R.dim)
  exact congrArg (fun f=>algebraMap ℚ _ (crossPointEval L R v w f)) h

lemma crossPointEval_inverseKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    Units.map (mapRing (crossPointEval L R v w)).toMonoidHom
      (rawInverseKernelUnit a L.dim R.dim)=
      ∏ i, ∏ j, ∏ x : Fin (L.dim i), ∏ y : Fin (R.dim j),
        affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-
          v (L.centerOfVar (L.varEquiv.symm ⟨i,x⟩))) ^ inverseExponent a i j := by
  simp only [rawInverseKernelUnit,rawFactor,map_prod,map_zpow,affineUnit_map,
    crossPointEval,map_sub,eval_X,Sum.elim_inl,Sum.elim_inr,Function.comp_apply]
end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
