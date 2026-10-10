import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionB

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct

noncomputable def extendPolynomial {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) :
    MvPolynomial α A →ₐ[ℚ] MvPolynomial β B :=
  ((rename j).restrictScalars ℚ).comp (mapAlgHom f)

@[simp] lemma extendPolynomial_C {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (a : A) :
    extendPolynomial f j (C a) = C (f a) := by
  simp [extendPolynomial]

@[simp] lemma extendPolynomial_X {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (i : α) :
    extendPolynomial f j (X i) = X (j i) := by
  simp [extendPolynomial]

lemma extendPolynomial_map {A B C α β : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) (j : α → β) (p : MvPolynomial α A) :
    map g.toRingHom (extendPolynomial f j p) = extendPolynomial (g.comp f) j p := by
  simp only [extendPolynomial,AlgHom.comp_apply,AlgHom.restrictScalars_apply,
    mapAlgHom_apply,map_rename,map_map,AlgHom.toRingHom_eq_coe]
  rfl

lemma extendPolynomial_preMap {A B C α β : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) (j : α → β) (p : MvPolynomial α A) :
    extendPolynomial g j (map f.toRingHom p) = extendPolynomial (g.comp f) j p := by
  simp only [extendPolynomial,AlgHom.comp_apply,AlgHom.restrictScalars_apply,
    mapAlgHom_apply,map_map,AlgHom.toRingHom_eq_coe]
  rfl

lemma toMvPolynomial_map {A B α : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (i : α) (p : Polynomial A) :
    map f.toRingHom (Polynomial.toMvPolynomial i p) =
      Polynomial.toMvPolynomial i (Polynomial.map f.toRingHom p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | monomial n a => simp [← Polynomial.C_mul_X_pow_eq_monomial]

end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

@[reducible] def Centers : SplitTree I → Type
  | .leaf _ => Unit
  | .node l r => l.Centers ⊕ r.Centers

noncomputable def centerTranslation (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d, A d →ₐ[ℚ] Polynomial (A d)) :
    (T : SplitTree I) → tensor A T →ₐ[ℚ] MvPolynomial T.Centers (tensor A T)
  | .leaf d => ((Polynomial.toMvPolynomial ()).restrictScalars ℚ).comp (τ d)
  | .node l r =>
    let L := (extendPolynomial (Algebra.TensorProduct.includeLeft :
      tensor A l →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inl).comp (centerTranslation A τ l)
    let R := (extendPolynomial (Algebra.TensorProduct.includeRight :
      tensor A r →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inr).comp (centerTranslation A τ r)
    Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma centerTranslation_tmul (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d, A d →ₐ[ℚ] Polynomial (A d)) (l r : SplitTree I)
    (x : tensor A l) (y : tensor A r) :
    centerTranslation A τ (.node l r) (x ⊗ₜ[ℚ] y) =
      extendPolynomial (Algebra.TensorProduct.includeLeft :
        tensor A l →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inl (centerTranslation A τ l x) *
      extendPolynomial (Algebra.TensorProduct.includeRight :
        tensor A r →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inr (centerTranslation A τ r y) := by
  rfl

omit [Fintype I] [DecidableEq I] in
lemma centerTranslation_natural (A C : (I → ℕ) → CommAlgCat.{u} ℚ)
    (f : ∀ d, A d →ₐ[ℚ] C d)
    (τ : ∀ d, A d →ₐ[ℚ] Polynomial (A d)) (υ : ∀ d, C d →ₐ[ℚ] Polynomial (C d))
    (h : ∀ d x, Polynomial.map (f d).toRingHom (τ d x) = υ d (f d x))
    (T : SplitTree I) (x : tensor A T) :
    map (tensorMap A C f T).toRingHom (centerTranslation A τ T x) =
      centerTranslation C υ T (tensorMap A C f T x) := by
  induction T with
  | leaf d =>
    change map (f d).toRingHom (Polynomial.toMvPolynomial () (τ d x)) =
      Polynomial.toMvPolynomial () (υ d (f d x))
    rw [toMvPolynomial_map,h]
  | node l r ihl ihr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change map (Algebra.TensorProduct.map (tensorMap A C f l) (tensorMap A C f r)).toRingHom
        (centerTranslation A τ (.node l r) (x ⊗ₜ[ℚ] y)) =
        centerTranslation C υ (.node l r) (tensorMap A C f l x ⊗ₜ[ℚ] tensorMap A C f r y)
      erw [centerTranslation_tmul,centerTranslation_tmul,map_mul]
      rw [extendPolynomial_map,extendPolynomial_map,← ihl x,← ihr y,
        extendPolynomial_preMap,extendPolynomial_preMap]
      rw [Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight]
    | add x y hx hy => simp only [map_add,hx,hy]

noncomputable def rawCenteredRestriction (T : SplitTree I) :
    S T.dim →ₐ[ℚ] MvPolynomial T.Centers (tensor rawFamily T) :=
  (centerTranslation rawFamily taylorS T).comp (rawRestriction T)

noncomputable def centeredRestrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) :
    B a (SlopeArithmetic.slope c η) T.dim →ₐ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
    (taylorB a (SlopeArithmetic.slope c η)) T).comp (restrictionB a c η hc θ T h)

theorem centeredRestrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) (f : S T.dim) :
    centeredRestrictionB a c η hc θ T h (quotientAlg a (SlopeArithmetic.slope c η) T.dim f) =
      map (quotientMap a (SlopeArithmetic.slope c η) T).toRingHom (rawCenteredRestriction T f) := by
  simp only [centeredRestrictionB,rawCenteredRestriction,AlgHom.comp_apply,restrictionB_mk]
  symm
  apply centerTranslation_natural
  intro d x
  exact (taylorB_mk a (SlopeArithmetic.slope c η) d x).symm

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
