import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Realization
import OAI.Combinatorics.Chromatic.Walls.Grid

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def sameDen (s t : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  ∏ i,∏ x ∈ s i,∏ y ∈ t i,diagonal (⟨i,x⟩ : Σi,A i) ⟨i,y⟩

noncomputable def arrowNum (a : I → I → ℕ) (s t : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  ∏ i,∏ j,∏ x ∈ s i,∏ y ∈ t j,diagonal (⟨i,x⟩ : Σi,A i) ⟨j,y⟩ ^ a i j

omit [∀ i,DecidableEq (A i)] in
lemma kernel_polynomial_ratio (a : I → I → ℕ) (s t : Pack (A:=A)) :
    kernel (pairKernel a) s t =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (arrowNum a s t) /
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen s t) := by
  rw [kernel_formula]
  simp only [arrowNum,sameDen,map_prod,map_pow]

omit [DecidableEq I] in
lemma sameDen_union_left (s t r : Pack (A:=A)) (h : ∀ i,Disjoint (s i) (t i)) :
    sameDen (fun i=>s i ∪ t i) r = sameDen s r * sameDen t r := by
  simp only [sameDen,Finset.prod_union (h _),Finset.prod_mul_distrib]

omit [DecidableEq I] in
lemma sameDen_union_right (s t r : Pack (A:=A)) (h : ∀ i,Disjoint (t i) (r i)) :
    sameDen s (fun i=>t i ∪ r i) = sameDen s t * sameDen s r := by
  simp only [sameDen,Finset.prod_union (h _),Finset.prod_mul_distrib]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma sameDen_ne_zero (s t : Pack (A:=A)) (h : ∀ i,Disjoint (s i) (t i)) :
    sameDen s t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  apply diagonal_ne_zero
  intro heq
  have hxy : x=y := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact Finset.disjoint_left.mp (h i) hx (hxy.symm ▸ hy)

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma sameDen_reverse_dvd (s t : Pack (A:=A)) : sameDen s t ∣ sameDen t s := by
  unfold sameDen
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  rw [Finset.prod_comm]
  apply Finset.prod_dvd_prod_of_dvd
  intro x hx
  apply Finset.prod_dvd_prod_of_dvd
  intro y hy
  refine ⟨-1,?_⟩
  simp only [diagonal]
  ring

noncomputable def crossDen (q₁ q₂ r₁ r₂ : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  sameDen q₁ r₂ * sameDen r₁ q₂

omit [DecidableEq I] in
lemma crossDen_dvd {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    crossDen (left q) (right q) (left r) (right r) ∣ sameDen (left p) (right p) := by
  have hq : (fun i=>left q i ∪ right q i) = left p := funext fun i=>(q i).property.2
  have hr : (fun i=>left r i ∪ right r i) = right p := funext fun i=>(r i).property.2
  conv_rhs => rw [← hq,← hr]
  rw [sameDen_union_left (left q) (right q) (fun i=>left r i ∪ right r i) (fun i=>(q i).property.1),
    sameDen_union_right (left q) (left r) (right r) (fun i=>(r i).property.1),
    sameDen_union_right (right q) (left r) (right r) (fun i=>(r i).property.1)]
  apply dvd_trans (mul_dvd_mul_left (sameDen (left q) (right r))
    (sameDen_reverse_dvd (left r) (right q)))
  refine ⟨sameDen (left q) (left r) * sameDen (right q) (right r),?_⟩
  ac_rfl

omit [DecidableEq I] in
lemma crossDen_ne_zero {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    crossDen (left q) (right q) (left r) (right r) ≠ 0 := by
  apply mul_ne_zero
  · exact sameDen_ne_zero _ _ (fun i=>(p i).property.1.mono (q i).left_subset (r i).right_subset)
  · exact sameDen_ne_zero _ _ (fun i=>(p i).property.1.symm.mono (r i).left_subset (q i).right_subset)

lemma crossKernel_polynomial (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    ∃ N : MvPolynomial (Σi,A i) ℚ,
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        kernel (pairKernel a) (left q) (right r) *
        kernel (pairKernel a) (left r) (right q) = algebraMap _ _ N := by
  obtain ⟨b,hb⟩ := crossDen_dvd p q r
  refine ⟨b * arrowNum a (left q) (right r) * arrowNum a (left r) (right q),?_⟩
  have hn := crossDen_ne_zero p q r
  have hn₁ : algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left q) (right r)) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne ((mul_ne_zero_iff.mp hn).1)
  have hn₂ : algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left r) (right q)) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne ((mul_ne_zero_iff.mp hn).2)
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,hb]
  simp only [crossDen,map_mul]
  field_simp

noncomputable def crossKernelPolynomial (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) : MvPolynomial (Σi,A i) ℚ :=
  (crossKernel_polynomial a p q r).choose

lemma crossKernelPolynomial_spec (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        kernel (pairKernel a) (left q) (right r) *
        kernel (pairKernel a) (left r) (right q) =
      algebraMap _ _ (crossKernelPolynomial a p q r) :=
  (crossKernel_polynomial a p q r).choose_spec

variable [∀ i,Fintype (A i)]

theorem shuffle_grid_cleared (a : I → I → ℕ)
    (f g : Pack (A:=A) → MvPolynomial (Σi,A i) ℚ)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
      PackConvolution.shuffle (pairKernel a)
        (fun t=>algebraMap _ _ (f t)) (fun t=>algebraMap _ _ (g t)) s =
      ∑ q : PackConvolution.Cut (left p), ∑ r : PackConvolution.Cut (right p),
        algebraMap _ _ (f (fun i=>left q i ∪ left r i) *
          g (fun i=>right q i ∪ right r i) * crossKernelPolynomial a p q r) *
          kernel (pairKernel a) (left q) (right q) *
          kernel (pairKernel a) (left r) (right r) := by
  rw [PackConvolution.shuffle_grid _ _ _ p]
  simp only [Finset.mul_sum,map_mul]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [← crossKernelPolynomial_spec]
  ring

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

abbrev CutShape (s : Pack (A:=A)) := ∀ i, Fin ((s i).card + 1)

def cutShape {s : Pack (A:=A)} (q : PackConvolution.Cut s) : CutShape s := fun i =>
  ⟨(left q i).card, Nat.lt_succ_of_le (Finset.card_le_card (q i).left_subset)⟩

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma cutShape_eq_iff {s : Pack (A:=A)} (q : PackConvolution.Cut s) (d : CutShape s) :
    cutShape q = d ↔ ∀ i,(left q i).card = (d i).val := by
  constructor
  · intro h i
    exact congrArg Fin.val (congrFun h i)
  · intro h
    exact funext fun i=>Fin.ext (h i)

noncomputable def cutByShape (s : Pack (A:=A)) :
    PackConvolution.Cut s ≃ Σ d : CutShape s,SizedCut (fun i=>(d i).val) s :=
  (Equiv.sigmaFiberEquiv (cutShape (s:=s))).symm.trans
    (Equiv.sigmaCongrRight fun d=>Equiv.subtypeEquivRight fun q=>cutShape_eq_iff q d)

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
@[simp] lemma cutByShape_snd (s : Pack (A:=A)) (q : PackConvolution.Cut s) :
    (cutByShape s q).2.val = q := rfl

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
@[simp] lemma cutByShape_symm {s : Pack (A:=A)}
    (d : CutShape s) (q : SizedCut (fun i=>(d i).val) s) :
    (cutByShape s).symm ⟨d,q⟩ = q.val := rfl

lemma sum_cut_by_shape {R : Type*} [AddCommMonoid R] (s : Pack (A:=A))
    (F : PackConvolution.Cut s → R) :
    ∑ q, F q = ∑ d : CutShape s,∑ q : SizedCut (fun i=>(d i).val) s,F q.val := by
  rw [← (cutByShape s).symm.sum_comp,Fintype.sum_sigma]
  rfl

lemma sum_grid_by_shape {R : Type*} [AddCommMonoid R] {s : Pack (A:=A)}
    (p : PackConvolution.Cut s)
    (F : PackConvolution.Cut (left p) → PackConvolution.Cut (right p) → R) :
    ∑ q,∑ r,F q r =
      ∑ d : CutShape (left p),∑ e : CutShape (right p),
        ∑ q : SizedCut (fun i=>(d i).val) (left p),
        ∑ r : SizedCut (fun i=>(e i).val) (right p),F q.val r.val := by
  rw [sum_cut_by_shape]
  simp_rw [sum_cut_by_shape (right p)]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.sum_comm

def shapeComplement {s : Pack (A:=A)} (d : CutShape s) : I → ℕ :=
  fun i=>(s i).card - (d i).val

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma shape_add_complement {s : Pack (A:=A)} (d : CutShape s) :
    (fun i=>(d i).val) + shapeComplement d = (fun i=>(s i).card) := by
  funext i
  exact Nat.add_sub_of_le (Nat.le_of_lt_succ (d i).isLt)

noncomputable def shapeRealization {s : Pack (A:=A)} (d : CutShape s) :
    Realization ((fun i=>(d i).val) + shapeComplement d) s :=
  defaultRealization (fun i=>(congrFun (shape_add_complement d) i).symm)

noncomputable def shapeCutEquiv {s : Pack (A:=A)} (d : CutShape s) :
    Cut (fun i=>(d i).val) (shapeComplement d) ≃ SizedCut (fun i=>(d i).val) s :=
  cutRealizationEquiv (shapeRealization d)

end ElementaryPositivity.RawShuffle

end

end OAI
