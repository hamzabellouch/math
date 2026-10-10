import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNExpansion

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma sameDen_reverse_eq (s t : Pack (A:=A)) :
    sameDen t s = (-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(s i).card*(t i).card) * sameDen s t := by
  unfold sameDen
  calc
    _ = ∏ i,∏ x∈s i,∏ y∈t i,
        (-1 : MvPolynomial (Σi,A i) ℚ)*diagonal ⟨i,x⟩ ⟨i,y⟩ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro x hx
      apply Finset.prod_congr rfl
      intro y hy
      unfold diagonal
      ring
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,←pow_mul]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.mul_comm _ _

omit [∀ i,Fintype (A i)] in
lemma crossKernelPolynomial_explicit (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    crossKernelPolynomial a p q r =
      (-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(right q i).card*(left r i).card) *
        sameDen (left q) (left r) * sameDen (right q) (right r) *
          arrowNum a (left q) (right r) * arrowNum a (left r) (right q) := by
  apply (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ)
    (FractionRing (MvPolynomial (Σi,A i) ℚ)))
  rw [←crossKernelPolynomial_spec,kernel_polynomial_ratio,kernel_polynomial_ratio]
  have hq : (fun i=>left q i ∪ right q i)=left p := funext fun i=>(q i).property.2
  have hr : (fun i=>left r i ∪ right r i)=right p := funext fun i=>(r i).property.2
  have hd : sameDen (left p) (right p)=
      sameDen (left q) (left r)*sameDen (left q) (right r)*
        ((-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(right q i).card*(left r i).card)*
          sameDen (left r) (right q))*sameDen (right q) (right r) := by
    conv_lhs => rw [←hq,←hr]
    rw [sameDen_union_left (left q) (right q) (fun i=>left r i ∪ right r i) (fun i=>(q i).property.1),
      sameDen_union_right (left q) (left r) (right r) (fun i=>(r i).property.1),
      sameDen_union_right (right q) (left r) (right r) (fun i=>(r i).property.1)]
    rw [sameDen_reverse_eq (left r) (right q)]
    have he : (∑ i,(left r i).card*(right q i).card)=∑ i,(right q i).card*(left r i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.mul_comm _ _
    rw [he]
    ring
  have hne := crossDen_ne_zero p q r
  have h₁ : algebraMap (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left q) (right r))≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne
        (mul_ne_zero_iff.mp hne).1
  have h₂ : algebraMap (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left r) (right q))≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne
        (mul_ne_zero_iff.mp hne).2
  rw [hd]
  simp only [map_mul,map_pow,map_neg,map_one]
  field_simp

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def fourForwardDifference (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ :=
  X (Sum.inr ((Equiv.sigmaSumDistrib _ _) ⟨j,y⟩)) -
    X (Sum.inl ((Equiv.sigmaSumDistrib _ _) ⟨i,x⟩))

omit [DecidableEq I] in
lemma fourSameDen11 (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (sameDen (left (canonicalLeftCut d₁ e₁ d₂ e₂)) (left (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ x:Fin (d₁ i),∏ y:Fin (d₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inl x) (.inl y) := by
  simp only [sameDen,map_prod,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] in
lemma fourSameDen22 (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (sameDen (right (canonicalLeftCut d₁ e₁ d₂ e₂)) (right (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ x:Fin (e₁ i),∏ y:Fin (e₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inr x) (.inr y) := by
  simp only [sameDen,map_prod,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] in
lemma fourArrow12 (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (arrowNum a (left (canonicalLeftCut d₁ e₁ d₂ e₂)) (right (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ j,∏ x:Fin (d₁ i),∏ y:Fin (e₂ j),fourForwardDifference d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)^a i j := by
  simp only [arrowNum,map_prod,map_pow,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma fourReverseDifference (d₁ e₁ d₂ e₂ : I → ℕ) (i j : I)
    (x : Fin (d₂ i)) (y : Fin (e₁ j)) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂)
      (ShufflePolynomiality.diagonal ⟨i,Sum.inr (Sum.inl x)⟩ ⟨j,Sum.inl (Sum.inr y)⟩)=
      -fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x) := by
  simp only [ShufflePolynomiality.diagonal,map_sub,rename_X]
  unfold fourForwardDifference
  rw [neg_sub]
  rfl

omit [DecidableEq I] in
lemma fourArrow21 (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (arrowNum a (left (canonicalRightCut d₁ e₁ d₂ e₂)) (right (canonicalLeftCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ j,∏ x:Fin (d₂ i),∏ y:Fin (e₁ j),(-fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))^a i j := by
  simp only [arrowNum,map_prod,map_pow,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  congr 1
  exact fourReverseDifference d₁ e₁ d₂ e₂ i j x y

lemma fourCrossPolynomial_explicit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourCrossPolynomial a d₁ e₁ d₂ e₂ =
      (-1 : MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) ^ (∑ i,e₁ i*d₂ i) *
      (∏ i,∏ x:Fin (d₁ i),∏ y:Fin (d₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inl x) (.inl y)) *
      (∏ i,∏ x:Fin (e₁ i),∏ y:Fin (e₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inr x) (.inr y)) *
      (∏ i,∏ j,∏ x:Fin (d₁ i),∏ y:Fin (e₂ j),fourForwardDifference d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)^a i j) *
      (∏ i,∏ j,∏ x:Fin (d₂ i),∏ y:Fin (e₁ j),(-fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))^a i j) := by
  rw [fourCrossPolynomial,crossKernelPolynomial_explicit]
  simp only [map_mul,map_pow,map_neg,map_one,fourSameDen11,fourSameDen22,fourArrow12,fourArrow21]
  congr 5
  simp only [canonicalLeftCut,canonicalRightCut,embedPackCut,sumPackCut,left,right,
    Finset.card_map,Finset.card_univ,Fintype.card_fin]

end ElementaryPositivity.RawShuffle

end

end OAI
