import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ManyBlockDiagonal

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A : Type*} [CommRing A]

noncomputable def ofTwo : Polynomial (Polynomial A) →+* MvPolynomial (Unit ⊕ Unit) A :=
  Polynomial.eval₂RingHom (Polynomial.toMvPolynomial (Sum.inl ())).toRingHom (X (Sum.inr ()))

@[simp] lemma ofTwo_C (p : Polynomial A) : ofTwo (Polynomial.C p) =
    Polynomial.toMvPolynomial (Sum.inl ()) p := by simp [ofTwo]

@[simp] lemma ofTwo_X : ofTwo (Polynomial.X : Polynomial (Polynomial A)) = X (Sum.inr ()) := by
  simp [ofTwo]

variable [Algebra ℚ A]

lemma evalRat_ofTwo (p : Polynomial (Polynomial A)) (v : Unit ⊕ Unit → ℚ) :
    evalRat v (ofTwo p) = RawShuffle.evalTwo p (v (Sum.inl ())) (v (Sum.inr ())) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,RawShuffle.evalTwo,Polynomial.eval_add] at *; rw [hp,hq]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,ofTwo_C,ofTwo_X,evalRat_X,
      RawShuffle.SplitTree.evalRat_toMvPolynomial,RawShuffle.evalTwo,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    rw [polynomial_eval_rat_algebraMap]

end ElementaryPositivity.CenterCalculus

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_two_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) (v : Unit ⊕ Unit → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) =
    TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d (v (Sum.inl ())))
      (translationB a (SlopeArithmetic.slope c η) e (v (Sum.inr ())))
      (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f) := by
  exact (centerTranslation_evalRat a (SlopeArithmetic.slope c η)
    (.node (.leaf d) (.leaf e)) _ v).trans
    (congrArg (translationAtB a (SlopeArithmetic.slope c η) (.node (.leaf d) (.leaf e)) v)
      (restrictionB_two a c η hc θ hd he f))

lemma twoLeading_eq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    {d e : I → ℕ} (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ) (p q : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    mapLinear (componentTensor a (SlopeArithmetic.slope c η) (.node (.leaf d) (.leaf e)) (p,q))
      (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) =
    ofTwo (bothLeading a c η hc (hd.2.trans he.2.symm) p q f) := by
  let μ := SlopeArithmetic.slope c η
  let l : (B a μ d ⊗[ℚ] B a μ e) →ₗ[ℚ] (B a μ d ⊗[ℚ] B a μ e) :=
    TensorProduct.map (componentB a μ d p) (componentB a μ e q)
  change mapLinear l _ = _
  apply eq_of_evalRat (A:=B a μ d ⊗[ℚ] B a μ e)
  intro v
  exact (evalRat_mapLinear l _ v).trans ((congrArg l
    (centeredRestrictionB_two_eval a c η hc θ hd he f v)).trans
    ((bothLeading_eval a c η hc (hd.2.trans he.2.symm) p q f _ _).symm.trans
      (evalRat_ofTwo (bothLeading a c η hc (hd.2.trans he.2.symm) p q f) v).symm))

theorem twoLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    (X (Sum.inl ()) - X (Sum.inr ())) ^ (-eulerForm a d e).toNat ∣
      mapLinear (componentTensor a (SlopeArithmetic.slope c η)
        (.node (.leaf d) (.leaf e)) (p,q))
        (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) := by
  rw [twoLeading_eq a c η hc θ hd he]
  have h := map_dvd ofTwo (bothLeading_diagonal_divisible a c η hc θ d e
    hd.1 he.1 hd.2 he.2 hsym p q W hw f hf)
  change ofTwo ((Polynomial.X-Polynomial.C Polynomial.X)^(-eulerForm a d e).toNat) ∣ _ at h
  simp only [map_pow,map_sub,ofTwo_X,ofTwo_C,Polynomial.toMvPolynomial_X] at h
  apply (pow_dvd_pow_of_dvd _ (-eulerForm a d e).toNat).trans h
  exact ⟨-1, ((mul_neg_one _).trans (neg_sub _ _)).symm⟩

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
universe u
variable {I : Type u}

def leafDimension : (T : SplitTree I) → T.Centers → I → ℕ
  | .leaf d, _ => d
  | .node l _, Sum.inl i => leafDimension l i
  | .node _ r, Sum.inr i => leafDimension r i

namespace Regroup

lemma leafDimension {T U : SplitTree I} (e : Regroup T U) (i : T.Centers) :
    U.leafDimension (e.centers i) = T.leafDimension i := by
  induction e with
  | refl T => rfl
  | assoc T U V => rcases i with (i|i)|i <;> rfl
  | swap T U => cases i <;> rfl
  | node e f ihe ihf => cases i with
    | inl i => exact ihe i
    | inr i => exact ihf i
  | trans e f ihe ihf => exact (ihf (e.centers i)).trans (ihe i)

def assocInv (T U V : SplitTree I) : Regroup (.node T (.node U V)) (.node (.node T U) V) :=
  (Regroup.swap T (.node U V)).trans
    ((Regroup.node (Regroup.swap U V) (Regroup.refl T)).trans
      ((Regroup.assoc V U T).trans
        ((Regroup.swap V (.node U T)).trans
          (Regroup.node (Regroup.swap U T) (Regroup.refl V)))))

@[simp] lemma assocInv_centers_left (T U V : SplitTree I) (i : T.Centers) :
    (assocInv T U V).centers (Sum.inl i) = Sum.inl (Sum.inl i) := rfl

@[simp] lemma assocInv_centers_mid (T U V : SplitTree I) (i : U.Centers) :
    (assocInv T U V).centers (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr i) := rfl

lemma isolate_one (T : SplitTree I) (i : T.Centers) :
    (∃ d, ∃ e : Regroup T (.leaf d), e.centers i = ()) ∨
    (∃ d U, ∃ e : Regroup T (.node (.leaf d) U), e.centers i = Sum.inl ()) := by
  induction T with
  | leaf d =>
    left
    exact ⟨d,.refl _,Subsingleton.elim _ _⟩
  | node l r ihl ihr =>
    cases i with
    | inl i =>
      rcases ihl i with ⟨d,e,he⟩ | ⟨d,U,e,he⟩
      · right
        refine ⟨d,r,.node e (.refl r),?_⟩
        exact congrArg Sum.inl he
      · right
        refine ⟨d,.node U r,(Regroup.node e (.refl r)).trans (Regroup.assoc _ _ _),?_⟩
        change (Equiv.sumAssoc _ _ _) (Sum.inl (e.centers i)) = _
        rw [he]
        rfl
    | inr i =>
      rcases ihr i with ⟨d,e,he⟩ | ⟨d,U,e,he⟩
      · right
        refine ⟨d,l,(Regroup.swap l r).trans (.node e (.refl l)),?_⟩
        exact congrArg Sum.inl he
      · right
        refine ⟨d,.node U l,(Regroup.swap l r).trans
          ((Regroup.node e (.refl l)).trans (Regroup.assoc _ _ _)),?_⟩
        change (Equiv.sumAssoc _ _ _) (Sum.inl (e.centers i)) = _
        rw [he]
        rfl

lemma isolate_pair (T : SplitTree I) (i j : T.Centers) (hij : i ≠ j) :
    (∃ d e, ∃ g : Regroup T (.node (.leaf d) (.leaf e)),
      g.centers i = Sum.inl () ∧ g.centers j = Sum.inr ()) ∨
    (∃ d e U, ∃ g : Regroup T (.node (.node (.leaf d) (.leaf e)) U),
      g.centers i = Sum.inl (Sum.inl ()) ∧ g.centers j = Sum.inl (Sum.inr ())) := by
  rcases isolate_one T i with ⟨d,g,hg⟩ | ⟨d,R,g,hg⟩
  · exact (hij (g.centers.injective (Subsingleton.elim _ _))).elim
  · cases hj : g.centers j with
    | inl t =>
      cases t
      exact (hij (g.centers.injective (hg.trans hj.symm))).elim
    | inr k =>
      rcases isolate_one R k with ⟨e,h,hh⟩ | ⟨e,U,h,hh⟩
      · left
        refine ⟨d,e,g.trans (.node (.refl _) h),?_,?_⟩
        · change (Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers i) = _
          rw [hg]
          rfl
        · change (Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers j) = _
          rw [hj]
          exact congrArg Sum.inr hh
      · right
        refine ⟨d,e,U,g.trans ((Regroup.node (.refl _) h).trans (assocInv _ _ _)),?_,?_⟩
        · change (assocInv _ _ _).centers
            ((Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers i)) = _
          rw [hg]
          rfl
        · change (assocInv _ _ _).centers
            ((Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers j)) = _
          rw [hj]
          change (assocInv _ _ _).centers (Sum.inr (h.centers k)) = _
          rw [hh]
          rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
