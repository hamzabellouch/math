import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.BothTaylorB
import OAI.Combinatorics.Chromatic.Shuffle.DimensionEquivBTrans
import OAI.Combinatorics.Chromatic.Walls.HNSpanning

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def pairRelativeCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (s : ℕ) (p q : ℤ) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e :=
  (polynomialCoeffLinear _ s).comp (relativeLeading a c η hc hs p q)

lemma pairRelativeCoefficient_wrong_degree (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (s : ℕ) (p q m : ℤ) (h : p+q ≠ m-s)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    pairRelativeCoefficient a c η hc hs s p q
      (componentB a (SlopeArithmetic.slope c η) (d+e) m f) = 0 := by
  exact relative_restriction_graded a c η hc hs (firstCut d e)
    (componentB a (SlopeArithmetic.slope c η) (d+e) m f) m ⟨f,rfl⟩ s p q h

namespace SplitTree

noncomputable def pairRefinementCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (s : ℕ) (p q : ℤ) (k : T.Degrees) :
    tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) →ₗ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η))
        (.node (.node (.leaf d) (.leaf e)) T) :=
  TensorProduct.map (pairRelativeCoefficient a c η hc hs s p q)
    (componentTensor a (SlopeArithmetic.slope c η) T k)

theorem pairRefinementCoefficient_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : d ≠ 0) (hdθ : SlopeArithmetic.slope c η d = θ)
    (heθ : SlopeArithmetic.slope c η e = θ)
    (hsym : eulerForm a d e = eulerForm a e d)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (p q W : ℤ) (k : T.Degrees)
    (hw : 2*(p+q+T.totalDegree k)+eulerForm a d d+eulerForm a e e+T.doubleShift a = W)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim))
    (hf : f ∈ sourceFiltration a c η hc θ ((d+e)+T.dim) W)
    (z : (SplitTree.node (.leaf (d+e)) T).Centers →₀ ℕ)
    (s : ℕ) (hs : s < (-eulerForm a d e).toNat) :
    pairRefinementCoefficient a c η hc (hdθ.trans heθ.symm) T s p q k
      ((centeredRestrictionB a c η hc θ (.node (.leaf (d+e)) T)
        ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd,
          (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ⟩,hT⟩ f).coeff z) = 0 := by
  classical
  let μ := SlopeArithmetic.slope c η
  let U : SplitTree I := .node (.leaf (d+e)) T
  have hU : U.OnSlope c η θ :=
    ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd,
      (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ⟩,hT⟩
  let x : tensor (quotientFamily a μ) U := (centeredRestrictionB a c η hc θ U hU f).coeff z
  let F := pairRefinementCoefficient a c η hc (hdθ.trans heθ.symm) T s p q k
  change F x = 0
  obtain ⟨t,ht,heq⟩ := componentTensor_finite_decomposition a μ U x
  have hterm : ∀ j ∈ t, F (componentTensor a μ U j x) = 0 := by
    intro j hj
    by_cases hk : k = j.2
    · subst k
      by_cases hm : p+q = j.1-s
      · have hsmall : 2*U.totalDegree j+U.doubleShift a < W := by
          change 2*(j.1+T.totalDegree j.2)+(eulerForm a (d+e) (d+e)+T.doubleShift a) < W
          rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,← hsym]
          have hs' : (s : ℤ) < -eulerForm a d e := Int.lt_toNat.mp hs
          linarith only [hs', hm, hw]
        have hz := sourceFiltration_allTrees a c η hc θ W f hf U hU rfl j z hsmall
        change componentTensor a μ U j x = 0 at hz
        rw [hz,map_zero]
      · generalize x = y
        induction y using TensorProduct.inductionOn with
        | tmul g h =>
          change pairRelativeCoefficient a c η hc (hdθ.trans heθ.symm) s p q
            (componentB a μ (d+e) j.1 g) ⊗ₜ[ℚ]
              componentTensor a μ T j.2 (componentTensor a μ T j.2 h) = 0
          change B a μ (d+e) at g
          rw [pairRelativeCoefficient_wrong_degree a c η hc (d := d) (e := e) (hdθ.trans heθ.symm) s p q j.1 hm, TensorProduct.zero_tmul]
        | add y y' hy hy' => simp only [map_add,hy,hy',add_zero]
    · generalize x = y
      induction y using TensorProduct.inductionOn with
      | tmul g h =>
        change pairRelativeCoefficient a c η hc (hdθ.trans heθ.symm) s p q
          (componentB a μ (d+e) j.1 g) ⊗ₜ[ℚ]
            componentTensor a μ T k (componentTensor a μ T j.2 h) = 0
        rw [componentTensor_componentTensor,ite_eq_right hk,TensorProduct.tmul_zero]
      | add y y' hy hy' => simp only [map_add,hy,hy',add_zero]
  calc
    F x = F (∑ j ∈ t, componentTensor a μ U j x) := congrArg F heq.symm
    _ = 0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

end SplitTree
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma evalRat_extendPolynomial {A D α β : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (f : A →ₐ[ℚ] D) (j : α → β)
    (p : MvPolynomial α A) (v : β → ℚ) :
    evalRat v (extendPolynomial f j p) = f (evalRat (v ∘ j) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [extendPolynomial]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    congr 1
    simp [extendPolynomial,evalRat]

lemma evalRat_toMvPolynomial {A α : Type*} [CommRing A] [Algebra ℚ A]
    (i : α) (p : Polynomial A) (v : α → ℚ) :
    evalRat v (Polynomial.toMvPolynomial i p) = p.eval (algebraMap ℚ A (v i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | monomial n a => simp [← Polynomial.C_mul_X_pow_eq_monomial]

lemma evalRat_mapAlgHom {A D α : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (f : A →ₐ[ℚ] D)
    (p : MvPolynomial α A) (v : α → ℚ) :
    evalRat v (map f.toRingHom p) = f (evalRat v p) := by
  have he : map f.toRingHom p = mapLinear f.toLinearMap p := by ext s; simp only [coeff_map,coeff_mapLinear,AlgHom.toLinearMap_apply]; rfl
  rw [he,evalRat_mapLinear]
  rfl

noncomputable def translationAtB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → (T.Centers → ℚ) →
      tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, v => translationB a μ d (v ())
  | .node l r, v => TensorProduct.map
      (translationAtB a μ l (v ∘ Sum.inl)) (translationAtB a μ r (v ∘ Sum.inr))

lemma centerTranslation_evalRat (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) (v : T.Centers → ℚ) :
    evalRat v (centerTranslation (quotientFamily a μ) (taylorB a μ) T x) =
      translationAtB a μ T v x := by
  induction T with
  | leaf d =>
    change B a μ d at x
    change evalRat v (Polynomial.toMvPolynomial () (taylorB a μ d x)) = _
    rw [evalRat_toMvPolynomial,taylorB_eval]
    rfl
  | node l r ihl ihr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      erw [centerTranslation_tmul,map_mul,evalRat_extendPolynomial,evalRat_extendPolynomial,ihl,ihr]
      change (translationAtB a μ l (v ∘ Sum.inl) x ⊗ₜ[ℚ] 1) *
        (1 ⊗ₜ[ℚ] translationAtB a μ r (v ∘ Sum.inr) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

noncomputable def polynomialOnLeft {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) : A ⊗[ℚ] Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
  let L : A →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q)).comp f
  let R : Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
    (Polynomial.CAlgHom : D ⊗[ℚ] Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q)).comp
      Algebra.TensorProduct.includeRight
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

lemma polynomialOnLeft_eval_tmul {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) (g : A) (h : Q) (t : ℚ) :
    (polynomialOnLeft f (g ⊗ₜ[ℚ] h)).eval (algebraMap ℚ _ t) =
      (f g).eval (algebraMap ℚ D t) ⊗ₜ[ℚ] h := by
  change (Polynomial.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q).toRingHom
      (f g) * Polynomial.C
        ((Algebra.TensorProduct.includeRight : Q →ₐ[ℚ] D ⊗[ℚ] Q) h)).eval _ = _
  rw [Polynomial.eval_mul,eval_map_rat,Polynomial.eval_C]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] h) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

lemma polynomialOnLeft_coeff_tmul {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) (g : A) (h : Q) (s : ℕ) :
    (polynomialOnLeft f (g ⊗ₜ[ℚ] h)).coeff s = (f g).coeff s ⊗ₜ[ℚ] h := by
  change (Polynomial.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q).toRingHom
      (f g) * Polynomial.C
        ((Algebra.TensorProduct.includeRight : Q →ₐ[ℚ] D ⊗[ℚ] Q) h)).coeff s = _
  rw [Polynomial.coeff_mul_C,Polynomial.coeff_map]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] h) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

noncomputable def pairRelativeRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) :
    tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) →ₐ[ℚ]
      Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η))
        (.node (.node (.leaf d) (.leaf e)) T)) :=
  polynomialOnLeft
    (D := tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf d) (.leaf e)))
    ((relativeTaylorB a (SlopeArithmetic.slope c η) d e).comp
      (RawShuffle.restrictionB a c η hc hs (firstCut d e)))

lemma pairRelativeRefinement_eval_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (g : B a (SlopeArithmetic.slope c η) (d+e))
    (h : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) (t : ℚ) :
    (pairRelativeRefinement a c η hc hs T (g ⊗ₜ[ℚ] h)).eval (algebraMap ℚ _ t) =
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e)
        (RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ] h := by
  erw [pairRelativeRefinement,polynomialOnLeft_eval_tmul]
  congr 1
  exact relativeTaylorB_eval a (SlopeArithmetic.slope c η) d e _ t

lemma pairRefinement_translationAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T))
    (v : Unit ⊕ T.Centers → ℚ) (t : ℚ) :
    translationAtB a (SlopeArithmetic.slope c η) (.node (.node (.leaf d) (.leaf e)) T)
      (relativePoint t v)
      (TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
        (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
          tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) x) =
    (pairRelativeRefinement a c η hc hs T
      (translationAtB a (SlopeArithmetic.slope c η) (.node (.leaf (d+e)) T) v x)).eval
        (algebraMap ℚ _ t) := by
  induction x using TensorProduct.inductionOn with
  | tmul g h =>
    let μ := SlopeArithmetic.slope c η
    change translationAtB a μ (.node (.node (.leaf d) (.leaf e)) T) (relativePoint t v)
      ((RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ] h) =
      (pairRelativeRefinement a c η hc hs T
        (translationB a μ (d+e) (v (Sum.inl ())) g ⊗ₜ[ℚ]
          translationAtB a μ T (v ∘ Sum.inr) h)).eval _
    erw [pairRelativeRefinement_eval_tmul a c η hc hs T,
      restrictionB_translation a c η hc hs (firstCut d e)]
    change TensorProduct.map (translationB a μ d (t+v (Sum.inl ())))
        (translationB a μ e (v (Sum.inl ())))
        (RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ]
          translationAtB a μ T (v ∘ Sum.inr) h = _
    congr 1
    generalize RawShuffle.restrictionB a c η hc hs (firstCut d e) g = y
    induction y using TensorProduct.inductionOn with
    | tmul f h =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,translationB_add]
      rfl
    | add y y' hy hy' => simp only [map_add,hy,hy']
  | add x y hx hy =>
    erw [map_add,map_add,map_add,map_add,Polynomial.eval_add]
    exact congrArg₂ (· + ·) hx hy

lemma pairRefinement_centerTranslation (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T)) :
    toRelative (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
      (taylorB a (SlopeArithmetic.slope c η)) (.node (.node (.leaf d) (.leaf e)) T)
        (TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
          (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
            tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) x)) =
      map (pairRelativeRefinement a c η hc hs T).toRingHom
        (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
          (taylorB a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) x) := by
  let μ := SlopeArithmetic.slope c η
  let U : SplitTree I := .node (.leaf (d+e)) T
  let V : SplitTree I := .node (.node (.leaf d) (.leaf e)) T
  let refine : tensor (quotientFamily a μ) U →ₗ[ℚ] tensor (quotientFamily a μ) V :=
    TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
      (LinearMap.id : tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T)
  let F := pairRelativeRefinement a c η hc hs T
  apply eq_of_evalRat
  intro v
  apply polynomial_eq_of_rat_evals
  intro t
  calc
    _ = evalRat (relativePoint t v)
        (centerTranslation (quotientFamily a μ) (taylorB a μ) V (refine x)) :=
      evalRat_toRelative _ v t
    _ = translationAtB a μ V (relativePoint t v) (refine x) :=
      centerTranslation_evalRat a μ V (refine x) (relativePoint t v)
    _ = (F (translationAtB a μ U v x)).eval (algebraMap ℚ _ t) :=
      pairRefinement_translationAtB a c η hc hs T x v t
    _ = (F (evalRat v (centerTranslation (quotientFamily a μ) (taylorB a μ) U x))).eval
        (algebraMap ℚ _ t) := by
      congr 2
      exact (centerTranslation_evalRat a μ U x v).symm
    _ = _ := congrArg (fun p => p.eval (algebraMap ℚ _ t))
      (evalRat_mapAlgHom F (centerTranslation (quotientFamily a μ) (taylorB a μ) U x) v).symm

lemma toRelative_mapLinear {A D α : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D)
    (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) :
    toRelative (mapLinear l p) = mapLinear (polynomialMapLinear l) (toRelative p) := by
  apply eq_of_evalRat
  intro v
  apply polynomial_eq_of_rat_evals
  intro t
  rw [evalRat_toRelative,evalRat_mapLinear,evalRat_mapLinear,
    polynomialMapLinear_eval_rat,evalRat_toRelative]

lemma pairRelativeRefinement_component_coeff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (s : ℕ) (p q : ℤ) (k : T.Degrees)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T)) :
    (polynomialMapLinear (componentTensor a (SlopeArithmetic.slope c η)
      (.node (.node (.leaf d) (.leaf e)) T) ((p,q),k))
        (pairRelativeRefinement a c η hc hs T x)).coeff s =
      pairRefinementCoefficient a c η hc hs T s p q k x := by
  rw [polynomialMapLinear_coeff]
  induction x using TensorProduct.inductionOn with
  | tmul g h =>
    erw [pairRelativeRefinement,polynomialOnLeft_coeff_tmul]
    rfl
  | add x y hx hy => simp only [map_add,Polynomial.coeff_add,hx,hy]

lemma restrictionB_two (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f =
      RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f := by
  let μ := SlopeArithmetic.slope c η
  change (Algebra.TensorProduct.map (AlgHom.id ℚ (B a μ d)) (AlgHom.id ℚ (B a μ e)))
    (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f) = _
  rw [Algebra.TensorProduct.map_id]
  rfl

lemma restrictionB_pairRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim)) :
    restrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T) ⟨⟨hd,he⟩,hT⟩ f =
      TensorProduct.map
        (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e)).toLinearMap
        (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
          tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
        (restrictionB a c η hc θ (.node (.leaf (d+e)) T)
          ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd.1,
            (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans hd.2⟩,hT⟩ f) := by
  let hs := (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans
    (hd.2.trans (slope_dim c η hc hT).symm)
  let y := RawShuffle.restrictionB a c η hc hs (firstCut (d+e) T.dim) f
  change Algebra.TensorProduct.map
      (restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩)
      (restrictionB a c η hc θ T hT) y =
    TensorProduct.map
      (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e)).toLinearMap
      (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
        tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
      (Algebra.TensorProduct.map (AlgHom.id ℚ _)
        (restrictionB a c η hc θ T hT) y)
  generalize y = x
  induction x using TensorProduct.inductionOn with
  | tmul g h =>
    change restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ g ⊗ₜ[ℚ]
      restrictionB a c η hc θ T hT h = _
    rw [restrictionB_two a c η hc θ hd he]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]; rfl

end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_pairRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim)) :
    toRelative (centeredRestrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T)
      ⟨⟨hd,he⟩,hT⟩ f) =
      map (pairRelativeRefinement a c η hc (hd.2.trans he.2.symm) T).toRingHom
        (centeredRestrictionB a c η hc θ (.node (.leaf (d+e)) T)
          ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd.1,
            (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans hd.2⟩,hT⟩ f) := by
  simp only [centeredRestrictionB,AlgHom.comp_apply]
  rw [restrictionB_pairRefinement a c η hc θ hd he T hT]
  exact pairRefinement_centerTranslation a c η hc (hd.2.trans he.2.symm) T _

theorem pairLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0<c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (hsym : eulerForm a d e = eulerForm a e d)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (p q W : ℤ) (k : T.Degrees)
    (hw : 2*(p+q+T.totalDegree k)+eulerForm a d d+eulerForm a e e+T.doubleShift a = W)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim))
    (hf : f ∈ sourceFiltration a c η hc θ ((d+e)+T.dim) W) :
    (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) ^ (-eulerForm a d e).toNat ∣
      mapLinear (componentTensor a (SlopeArithmetic.slope c η)
        (.node (.node (.leaf d) (.leaf e)) T) ((p,q),k))
          (centeredRestrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T)
            ⟨⟨hd,he⟩,hT⟩ f) := by
  apply diagonal_dvd_of_relative_coeff
  intro z s hs
  rw [toRelative_mapLinear,centeredRestrictionB_pairRefinement a c η hc θ hd he T hT,
    coeff_mapLinear,coeff_map]
  exact (pairRelativeRefinement_component_coeff a c η hc (hd.2.trans he.2.symm) T s p q k _).trans
    (pairRefinementCoefficient_zero a c η hc θ hd.1 hd.2 he.2 hsym T hT p q W k hw f hf z s hs)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
