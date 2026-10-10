import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DimensionGrid
import OAI.Combinatorics.Chromatic.Shuffle.CellLeadingSum
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGrade

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
lemma mk_eq_mk_iff_sub_mem (F G : Submodule ℚ M) (x y : F) :
    mk F G x = mk F G y ↔ x.val-y.val∈G := by
  rw [←sub_eq_zero,←map_sub]
  exact Submodule.Quotient.mk_eq_zero _
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open ElementaryPositivity.PackConvolution ElementaryPositivity.LinearDetection
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma unitalSourceTensorFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) :
    Antitone (unitalSourceTensorFiltration a c η hc θ d e) :=
  additiveTensorFiltration_antitone _ _

lemma gridLeadingB_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η (slope c η α))
    (h : d+e=α+β) (hd : OnSlopeOrZero c η (slope c η α) d)
    (he : OnSlopeOrZero c η (slope c η α) e) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc (slope c η α) d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc (slope c η α) e V)
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    gridLeadingB a c η hc (slope c η α) f g (cutRealizationEquiv R (firstCut α β)).val
      (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
      unitalSourceTensorFiltration a c η hc (slope c η α) α β (U+V) := by
  have hz : quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g))∈
      unitalSourceFiltration a c η hc (slope c η α) (α+β) (U+V) := by
    rw [←castB_mk]
    exact castB_mem_unitalSourceFiltration a c η hc (slope c η α) h (U+V)
      (shuffleBUnit_filtered a c η hc (slope c η α) hχ d e hd he U V _ _ hf hg)
  have hC := unitalSeparationSeries_coeff_filtration a c η hc (slope c η α) α β
    (Or.inr (Or.inr ht)) (U+V) 0 _ hz
  have hdiff := unitalSeparationConstant_shuffle_leading a c η hc hχ h U V f g hf hg ht hs R
  have hdiff' := unitalSourceTensorFiltration_antitone a c η hc (slope c η α) α β
    (show U+V≤U+V+1 by omega) hdiff
  simpa only [sub_sub_cancel] using Submodule.sub_mem _ hC hdiff'

noncomputable def gridLeadingGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η (slope c η α))
    (h : d+e=α+β) (hd : OnSlopeOrZero c η (slope c η α) d)
    (he : OnSlopeOrZero c η (slope c η α) e) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc (slope c η α) d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc (slope c η α) e V)
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    UnitalSourceTensorGrade a c η hc (slope c η α) α β (U+V) :=
  Submodule.Quotient.mk ⟨_,gridLeadingB_mem a c η hc hχ h hd he U V f g hf hg ht hs R⟩

lemma unitalGradeCoproduct_shuffle_grid (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η (slope c η α))
    (h : d+e=α+β) (hd : OnSlopeOrZero c η (slope c η α) d)
    (he : OnSlopeOrZero c η (slope c η α) e) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc (slope c η α) d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc (slope c η α) e V)
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    unitalGradeCoproduct a c η hc (slope c η α) α β (Or.inr (Or.inr ht)) (U+V)
      (Submodule.Quotient.mk
        ⟨castB a (slope c η) h (shuffleBUnit a c η hc d e (hd.compatible he)
          (quotientAlg a (slope c η) d f) (quotientAlg a (slope c η) e g)),
         castB_mem_unitalSourceFiltration a c η hc (slope c η α) h (U+V)
          (shuffleBUnit_filtered a c η hc (slope c η α) hχ d e hd he U V _ _ hf hg)⟩)=
      gridLeadingGrade a c η hc hχ h hd he U V f g hf hg ht hs R := by
  rw [unitalGradeCoproduct_mk]
  apply (mk_eq_mk_iff_sub_mem _ _ _ _).mpr
  change (unitalSeparationSeries a c η hc (Or.inr (Or.inr ht))
    (castB a (slope c η) h (quotientAlg a (slope c η) (d+e) (shufflePolynomial a f g)))).coeff 0-
    gridLeadingB a c η hc (slope c η α) f g (cutRealizationEquiv R (firstCut α β)).val
      (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈_
  rw [castB_mk]
  exact unitalSeparationConstant_shuffle_leading a c η hc hχ h U V f g hf hg ht hs R
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

def cutShapeDimensionEquiv {d : I → ℕ} {s : Pack (A:=A)} (R : Realization d s) :
    CutShape s ≃ DimensionSplit d :=
  Equiv.piCongrRight fun i => finCongr (congrArg (·+1) (congrFun (realization_card R) i))

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
@[simp] lemma cutShapeDimensionEquiv_left {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) (u : CutShape s) :
    DimensionSplit.left (cutShapeDimensionEquiv R u) = (fun i=>(u i).val) := rfl

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
@[simp] lemma cutShapeDimensionEquiv_right {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) (u : CutShape s) :
    DimensionSplit.right (cutShapeDimensionEquiv R u) = shapeComplement u := by
  funext i
  change d i-(u i).val=(s i).card-(u i).val
  exact congrArg (fun n=>n-(u i).val) (congrFun (realization_card R) i).symm

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
lemma sum_cutShapeDimensionEquiv {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) {M : Type*} [AddCommMonoid M] (F : DimensionSplit d → M) :
    ∑ u : CutShape s,F (cutShapeDimensionEquiv R u)=∑ u : DimensionSplit d,F u :=
  Equiv.sum_comp (cutShapeDimensionEquiv R) F

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def dimensionRowLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (u : DimensionSplit α) (v : DimensionSplit β) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  if hon : CellsOnSlope c η θ (left u) (right u) (left v) (right v) then
    castBTensor a (slope c η) (left_add_right u) (left_add_right v)
      (cellLeadingB a c η hc θ (left u) (right u) (left v) (right v) hon f g)
  else 0

noncomputable def dimensionLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  ∑ u : DimensionSplit α,∑ v : DimensionSplit β,dimensionRowLeadingB a c η hc θ f g u v

lemma cast_cellLeadingB_congr (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {p q r s p' q' r' s' : I → ℕ}
    (hp : p=p') (hq : q=q') (hr : r=r') (hs : s=s')
    (h₁ : p+q=α) (h₂ : r+s=β) (h₁' : p'+q'=α) (h₂' : r'+s'=β)
    (hon : CellsOnSlope c η θ p q r s) (hon' : CellsOnSlope c η θ p' q' r' s') :
    castBTensor a (slope c η) h₁ h₂ (cellLeadingB a c η hc θ p q r s hon f g)=
      castBTensor a (slope c η) h₁' h₂' (cellLeadingB a c η hc θ p' q' r' s' hon' f g) := by
  subst p'; subst q'; subst r'; subst s'
  rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [∀ index, Fintype (A index)] in
lemma gridLeadingB_eq_dimensionLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (PackConvolution.left p))
    (T : Realization β (PackConvolution.right p)) :
    gridLeadingB a c η hc θ f g p R T=dimensionLeadingB (α:=α) (β:=β) a c η hc θ f g := by
  unfold gridLeadingB dimensionLeadingB
  calc
    _=∑ u : CutShape (PackConvolution.left p),∑ v : CutShape (PackConvolution.right p),
      dimensionRowLeadingB a c η hc θ f g (cutShapeDimensionEquiv R u) (cutShapeDimensionEquiv T v) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        unfold dimensionRowLeadingB gridShapeLeadingB
        split_ifs with hon hon'
        · exact cast_cellLeadingB_congr a c η hc θ f g rfl
            (cutShapeDimensionEquiv_right R u).symm rfl
            (cutShapeDimensionEquiv_right T v).symm _ _ _ _ hon hon'
        · exact False.elim (hon' (by simpa only [cutShapeDimensionEquiv_left,
            cutShapeDimensionEquiv_right] using hon))
        · rename_i hon'
          exact False.elim (hon (by simpa only [cutShapeDimensionEquiv_left,
            cutShapeDimensionEquiv_right] using hon'))
        · rfl
    _=_ := by
      simp_rw [sum_cutShapeDimensionEquiv]
      exact sum_cutShapeDimensionEquiv R (fun u =>
        ∑ v : DimensionSplit β,dimensionRowLeadingB a c η hc θ f g u v)

end ElementaryPositivity.RawShuffle

end

end OAI
