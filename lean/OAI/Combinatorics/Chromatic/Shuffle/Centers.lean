import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Regroup

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma extendPolynomial_comp {A B C α β γ : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) (j : α → β) (k : β → γ) (p : MvPolynomial α A) :
    extendPolynomial g k (extendPolynomial f j p)=extendPolynomial (g.comp f) (k∘j) p := by
  simp only [extendPolynomial,AlgHom.comp_apply,AlgHom.restrictScalars_apply,mapAlgHom_apply,
    map_rename,rename_rename,map_map]
  rfl

namespace Regroup
noncomputable def centers {T U : SplitTree I} : Regroup T U → T.Centers ≃ U.Centers
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.sumAssoc _ _ _
  | .swap _ _ => Equiv.sumComm _ _
  | .node f g => Equiv.sumCongr f.centers g.centers
  | .trans f g => f.centers.trans g.centers

omit [Fintype I] [DecidableEq I] in
lemma centerTranslation_natural (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d,A d →ₐ[ℚ] Polynomial (A d)) {T U : SplitTree I}
    (e : Regroup T U) (x : tensor A T) :
    centerTranslation A τ U (e.equivalence A x)=
      extendPolynomial (e.equivalence A).toAlgHom e.centers (centerTranslation A τ T x) := by
  induction e with
  | refl T =>
    change centerTranslation A τ T x=
      rename id (map (RingHom.id _) (centerTranslation A τ T x))
    simp only [map_id,rename_id,AlgHom.id_apply]
  | assoc T U V =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y =>
        change centerTranslation A τ (.node T (.node U V)) (x ⊗ₜ[ℚ] (y ⊗ₜ[ℚ] z))=_
        rw [centerTranslation_tmul A τ T (.node U V),centerTranslation_tmul A τ U V,
          centerTranslation_tmul A τ (.node T U) V,centerTranslation_tmul A τ T U]
        simp only [map_mul,extendPolynomial_comp]
        rw [mul_assoc]
        congr 1
  | swap T U =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change centerTranslation A τ (.node U T) (y ⊗ₜ[ℚ] x)=_
      rw [centerTranslation_tmul A τ U T,centerTranslation_tmul A τ T U,map_mul,
        extendPolynomial_comp,extendPolynomial_comp,mul_comm]
      congr 1
  | node e g ihe ihg =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change centerTranslation A τ (.node _ _) (e.equivalence A x ⊗ₜ[ℚ] g.equivalence A y)=_
      rw [centerTranslation_tmul,ihe,ihg,centerTranslation_tmul,map_mul,
        extendPolynomial_comp,extendPolynomial_comp,extendPolynomial_comp,extendPolynomial_comp]
      congr 1 <;> congr 2 <;> apply AlgHom.ext <;> intro t
      · change e.equivalence A t ⊗ₜ[ℚ] (1 : tensor A _) =
          e.equivalence A t ⊗ₜ[ℚ] g.equivalence A 1
        rw [map_one]
      · change (1 : tensor A _) ⊗ₜ[ℚ] g.equivalence A t =
          e.equivalence A 1 ⊗ₜ[ℚ] g.equivalence A t
        rw [map_one]
  | trans e g ihe ihg =>
    change centerTranslation A τ _ (g.equivalence A (e.equivalence A x))=_
    rw [ihg,ihe,extendPolynomial_comp]
    rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SplitTree.Regroup
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    centeredRestrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (centeredRestrictionB a c η hc θ T hT f) := by
  change centerTranslation _ _ U (restrictionB a c η hc θ U hU
    (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f))=_
  rw [← restrictionB_natural a c η hc θ e hT hU f]
  erw [centerTranslation_natural]
  rfl

lemma extendPolynomial_coeff {A C α β : Type*} [CommRing A] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ C] (f : A →ₐ[ℚ] C) (e : α ≃ β)
    (p : MvPolynomial α A) (z : α →₀ ℕ) :
    (extendPolynomial f e p).coeff (z.mapDomain e)=f (p.coeff z) := by
  change (rename e (map f.toRingHom p)).coeff (z.mapDomain e)=_
  rw [coeff_rename_mapDomain e e.injective,coeff_map]
  rfl

lemma centeredRestrictionB_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (z : T.Centers →₀ ℕ) :
    (centeredRestrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)).coeff (z.mapDomain e.centers)=
      e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        ((centeredRestrictionB a c η hc θ T hT f).coeff z) := by
  rw [centeredRestrictionB_natural]
  exact extendPolynomial_coeff _ _ _ _

end ElementaryPositivity.RawShuffle.SplitTree.Regroup

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace Regroup
noncomputable def degrees {T U : SplitTree I} : Regroup T U → T.Degrees ≃ U.Degrees
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.prodAssoc _ _ _
  | .swap _ _ => Equiv.prodComm _ _
  | .node f g => Equiv.prodCongr f.degrees g.degrees
  | .trans f g => f.degrees.trans g.degrees

omit [Fintype I] [DecidableEq I] in
lemma totalDegree {T U : SplitTree I} (e : Regroup T U) (k : T.Degrees) :
    U.totalDegree (e.degrees k)=T.totalDegree k := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact (add_assoc _ _ _).symm
  | swap T U => exact add_comm _ _
  | node e f ihe ihf => exact congrArg₂ (·+·) (ihe k.1) (ihf k.2)
  | trans e f ihe ihf => exact (ihf (e.degrees k)).trans (ihe k)

omit [DecidableEq I] in
lemma doubleShift (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U) :
    U.doubleShift a=T.doubleShift a := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact (add_assoc _ _ _).symm
  | swap T U => exact add_comm _ _
  | node e f ihe ihf => exact congrArg₂ (·+·) ihe ihf
  | trans e f ihe ihf => exact ihf.trans ihe

omit [DecidableEq I] in
lemma onSlope (c η : I → ℝ) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U) :
    T.OnSlope c η θ → U.OnSlope c η θ := by
  induction e with
  | refl T => exact id
  | assoc T U V => exact fun h=>⟨h.1.1,h.1.2,h.2⟩
  | swap T U => exact fun h=>⟨h.2,h.1⟩
  | node e f ihe ihf => exact fun h=>⟨ihe h.1,ihf h.2⟩
  | trans e f ihe ihf => exact ihf∘ihe

lemma componentTensor_natural (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {T U : SplitTree I} (e : Regroup T U) (k : T.Degrees)
    (x : tensor (quotientFamily a μ) T) :
    e.equivalence (quotientFamily a μ) (componentTensor a μ T k x)=
      componentTensor a μ U (e.degrees k) (e.equivalence (quotientFamily a μ) x) := by
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
      change e.equivalence (quotientFamily a μ) (componentTensor a μ _ k.1 x) ⊗ₜ[ℚ]
          g.equivalence (quotientFamily a μ) (componentTensor a μ _ k.2 y)=
        componentTensor a μ _ (e.degrees k.1) (e.equivalence (quotientFamily a μ) x) ⊗ₜ[ℚ]
          componentTensor a μ _ (g.degrees k.2) (g.equivalence (quotientFamily a μ) y)
      rw [ihe,ihg]
  | trans e g ihe ihg =>
    change g.equivalence (quotientFamily a μ)
      (e.equivalence (quotientFamily a μ) (componentTensor a μ _ k x))=_
    rw [ihe,ihg]
    rfl

omit [Fintype I] [DecidableEq I] in
lemma append_ordered (T : SplitTree I) (hT : T.IsOrderedList)
    (U : SplitTree I) (hU : U.IsOrderedList) :
    ∃ V : SplitTree I,V.IsOrderedList ∧ Nonempty (Regroup (.node T U) V) := by
  induction T with
  | leaf d => exact ⟨.node (.leaf d) U,hU,⟨.refl _⟩⟩
  | node l r ihl ihr =>
    cases l with
    | node l₁ l₂ => exact False.elim hT
    | leaf d =>
      obtain ⟨V,hV,⟨e⟩⟩ := ihr hT
      exact ⟨.node (.leaf d) V,hV,⟨(Regroup.assoc _ _ _).trans (.node (.refl _) e)⟩⟩

omit [Fintype I] [DecidableEq I] in
lemma ordered_normalization (T : SplitTree I) :
    ∃ U : SplitTree I,U.IsOrderedList ∧ Nonempty (Regroup T U) := by
  induction T with
  | leaf d => exact ⟨.leaf d,True.intro,⟨.refl _⟩⟩
  | node l r ihl ihr =>
    obtain ⟨L,hL,⟨e⟩⟩ := ihl
    obtain ⟨R,hR,⟨f⟩⟩ := ihr
    obtain ⟨V,hV,⟨g⟩⟩ := append_ordered L hL R hR
    exact ⟨V,hV,⟨(Regroup.node e f).trans g⟩⟩

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
