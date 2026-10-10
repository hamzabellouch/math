import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGrade

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LaurentAtInfinity
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA unitalSepTensorN unitalSepTensorM

lemma unitalSeparationConstant_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (d : I → ℕ) (f : B a (slope c η) d) :
    unitalSeparationConstant a c η hc 0 d (Or.inl rfl)
      (castB a (slope c η) (zero_add d).symm f) =
      (1 : B a (slope c η) 0) ⊗ₜ[ℚ] f := by
  change ((quotientInverseKernelUnit a (slope c η) 0 d).val *
    polynomial (unitalRestrictionRelativeB a c η hc (Or.inl rfl)
      (castB a (slope c η) (zero_add d).symm f))).coeff 0 = _
  rw [quotientInverseKernelUnit_zero_left, Units.val_one, one_mul]
  rw [show (0 : ℤ) = -(0 : ℕ) by simp, polynomial_coeff]
  change (relativeTaylorB a (slope c η) 0 d
    (restrictionBUnit a c η hc (Or.inl rfl) (firstCut 0 d)
      (castB a (slope c η) (zero_add d).symm f))).coeff 0 = _
  rw [relativeTaylorB_coeff_zero, restrictionBUnit_zero_left]

lemma unitalSeparationConstant_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (d : I → ℕ) (f : B a (slope c η) d) :
    unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))
      (castB a (slope c η) (add_zero d).symm f) =
      f ⊗ₜ[ℚ] (1 : B a (slope c η) 0) := by
  change ((quotientInverseKernelUnit a (slope c η) d 0).val *
    polynomial (unitalRestrictionRelativeB a c η hc (Or.inr (Or.inl rfl))
      (castB a (slope c η) (add_zero d).symm f))).coeff 0 = _
  rw [quotientInverseKernelUnit_zero_right, Units.val_one, one_mul]
  rw [show (0 : ℤ) = -(0 : ℕ) by simp, polynomial_coeff]
  change (relativeTaylorB a (slope c η) d 0
    (restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) (firstCut d 0)
      (castB a (slope c η) (add_zero d).symm f))).coeff 0 = _
  rw [relativeTaylorB_coeff_zero, restrictionBUnit_zero_right]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma extendPolynomial_map_algebra {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (p : MvPolynomial α ℚ) :
    extendPolynomial f j (map (algebraMap ℚ A) p)=
      map (algebraMap ℚ B) (rename j p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [map_C,extendPolynomial_C,AlgHom.commutes,rename_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,map_X,extendPolynomial_X,rename_X,hp]

omit [Fintype I] [DecidableEq I] in
lemma node_le_iff (T U : SplitTree I) (x y : (SplitTree.node T U).Centers) :
    @LE.le _ (centersLinearOrder (SplitTree.node T U)).toLE x y ↔
      Sum.Lex (· ≤ · : T.Centers → T.Centers → Prop)
      (· ≤ · : U.Centers → U.Centers → Prop) x y := Iff.rfl

namespace Regroup
lemma filtrationDimensionEquiv_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (filtrationDimensionEquiv a c η hc θ h W f).val=
      dimensionEquivB a (SlopeArithmetic.slope c η) h f.val := by
  subst e
  rfl

lemma weightComponent_natural (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {T U : SplitTree I} (e : Regroup T U) (W : ℤ) (x : tensor (quotientFamily a μ) T) :
    e.equivalence (quotientFamily a μ) (weightComponent a μ T W x)=
      weightComponent a μ U W (e.equivalence (quotientFamily a μ) x) := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ U
  intro k
  rw [map_sub]
  apply sub_eq_zero.mpr
  obtain ⟨j,rfl⟩:=e.degrees.surjective k
  rw [←componentTensor_natural,componentTensor_weightComponent,
    componentTensor_weightComponent,e.totalDegree,e.doubleShift]
  split_ifs
  · exact componentTensor_natural a μ e j x
  · exact map_zero _

lemma totalLeadingPolynomial_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    totalLeadingPolynomial a c η hc θ U hU W
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (totalLeadingPolynomial a c η hc θ T hT W f) := by
  unfold totalLeadingPolynomial
  rw [centeredRestrictionB_natural]
  exact mapLinear_extendPolynomial _ _ _ _ (fun x=>(weightComponent_natural a _ e W x).symm) _

def OrderPreserving {T U : SplitTree I} (e : Regroup T U) : Prop :=
  ∀ i j : T.Centers,e.centers i<e.centers j ↔ i<j

omit [Fintype I] [DecidableEq I] in
lemma assoc_orderPreserving (T U V : SplitTree I) : OrderPreserving (.assoc T U V) := by
  intro i j
  change Sum.Lex (· < · : T.Centers → T.Centers → Prop)
      (Sum.Lex (· < · : U.Centers → U.Centers → Prop) (· < · : V.Centers → V.Centers → Prop))
      ((Equiv.sumAssoc T.Centers U.Centers V.Centers) i)
      ((Equiv.sumAssoc T.Centers U.Centers V.Centers) j) ↔
    Sum.Lex (Sum.Lex (· < · : T.Centers → T.Centers → Prop) (· < · : U.Centers → U.Centers → Prop))
      (· < · : V.Centers → V.Centers → Prop) i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [Equiv.sumAssoc,Sum.lex_inl_inl,Sum.lex_inr_inr,Sum.lex_inr_inl,Sum.Lex.sep]

omit [DecidableEq I] in
lemma centerPower_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (φ : ℤ → ℕ) :
    rename e.centers (∏ ij∈T.centerPairs,
      diagonal ij.1 ij.2 ^ φ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)))=
      ∏ ij∈U.centerPairs,
        diagonal ij.1 ij.2 ^ φ (eulerForm a (U.leafDimension ij.1) (U.leafDimension ij.2)) := by
  classical
  simp only [centerPairs,Finset.prod_filter,map_prod,apply_ite,map_pow,map_one,
    diagonal,map_sub,rename_X]
  apply Fintype.prod_equiv (Equiv.prodCongr e.centers e.centers)
  intro ij
  simp only [Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,he ij.1 ij.2,e.leafDimension]

omit [DecidableEq I] in
lemma centerNumerator_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) :
    rename e.centers (centerNumerator a T T.centerPairs)=centerNumerator a U U.centerPairs :=
  centerPower_natural a e he Int.toNat

omit [DecidableEq I] in
lemma centerDenominator_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) :
    rename e.centers (centerDenominator a T T.centerPairs)=centerDenominator a U U.centerPairs :=
  centerPower_natural a e he (fun z=>(-z).toNat)

lemma clearedLeading_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (hχT : T.PairSymmetric a) (hχU : U.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    clearedLeading a c η hc θ U hU hχU W
        (filtrationDimensionEquiv a c η hc θ e.dimension W f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (clearedLeading a c η hc θ T hT hχT W f) := by
  apply scalar_mul_injective _ (centerDenominator_ne_zero a U)
  dsimp only
  rw [denominator_clearedLeading,filtrationDimensionEquiv_val,totalLeadingPolynomial_natural]
  conv_rhs => lhs; rw [←centerDenominator_natural a e he]
  rw [←extendPolynomial_map_algebra
    (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom e.centers,
    ←map_mul,denominator_clearedLeading]

lemma normalizedSymbol_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (hχT : T.PairSymmetric a) (hχU : U.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    normalizedSymbol a c η hc θ U hU hχU W
        (filtrationDimensionEquiv a c η hc θ e.dimension W f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (normalizedSymbol a c η hc θ T hT hχT W f) := by
  change map _ (centerNumerator a U U.centerPairs)*clearedLeading a c η hc θ U hU hχU W _=
    extendPolynomial _ _ (map _ (centerNumerator a T T.centerPairs)*clearedLeading a c η hc θ T hT hχT W f)
  rw [clearedLeading_natural a c η hc θ e he hT hU hχT hχU W f,map_mul,
    extendPolynomial_map_algebra,centerNumerator_natural a e he]

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
