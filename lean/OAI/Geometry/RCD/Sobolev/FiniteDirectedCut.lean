import Mathlib

namespace OAI

/-! # A directed cut captures one quarter of the off-diagonal weight

The finite counting step in Rajala--Sturm, Lemma 3.1. Averaging over all
Boolean cuts is implemented by the two coordinate-flip bijections.
-/

open Finset
noncomputable section
namespace RegularPointCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def flipColor (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun b k := if k=i then !(b k) else b k
  invFun b k := if k=i then !(b k) else b k
  left_inv := by
    intro b
    funext k
    by_cases hk : k=i <;> simp [hk]
  right_inv := by
    intro b
    funext k
    by_cases hk : k=i <;> simp [hk]

def directedCutWeight (w : ι → ι → ℝ) (b : ι → Bool) : ℝ :=
  ∑ i, ∑ j, if b i=true ∧ b j=false then w i j else 0

private theorem four_color_sum (i j : ι) (hij : i≠j) (a : ℝ) :
    4*(∑ b : ι → Bool, if b i=true ∧ b j=false then a else 0)=
      (Fintype.card (ι → Bool):ℝ)*a := by
  let F := fun b : ι → Bool => if b i=true ∧ b j=false then a else 0
  have hflip (e : (ι → Bool) ≃ (ι → Bool)) : (∑ b, F (e b))=∑ b, F b :=
    e.sum_comp F
  have hpoint (b : ι → Bool) :
      F b+F (flipColor i b)+F (flipColor j b)+F (flipColor i (flipColor j b))=a := by
    cases hi : b i <;> cases hj : b j <;> simp [F,flipColor,hij,hij.symm,hi,hj]
  have h := congrArg (fun f : (ι → Bool) → ℝ => ∑ b, f b) (funext hpoint)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  rw [hflip (flipColor i),hflip (flipColor j)] at h
  have hboth : (∑ b, F (flipColor i (flipColor j b)))=∑ b, F b := by
    exact ((flipColor j).sum_comp (fun b => F (flipColor i b))).trans (hflip (flipColor i))
  rw [hboth] at h
  change 4*(∑ b, F b)=_
  linarith only [h]

theorem sum_directedCutWeight (w : ι → ι → ℝ) (hdiag : ∀ i, w i i=0) :
    4*(∑ b : ι → Bool, directedCutWeight w b)=
      (Fintype.card (ι → Bool):ℝ)*(∑ i, ∑ j, w i j) := by
  unfold directedCutWeight
  have hs : (∑ b : ι → Bool, ∑ i, ∑ j, if b i=true ∧ b j=false then w i j else 0)=
      ∑ i, ∑ j, ∑ b : ι → Bool, if b i=true ∧ b j=false then w i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hs]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j
    simp [hdiag]
  · simpa only [Finset.mul_sum] using four_color_sum i j hij (w i j)

theorem exists_directedCutWeight_ge_quarter (w : ι → ι → ℝ) (hdiag : ∀ i, w i i=0) :
    ∃ b : ι → Bool, (∑ i, ∑ j, w i j)/4≤directedCutWeight w b := by
  by_contra h
  have h : ∀ b : ι → Bool, directedCutWeight w b<(∑ i, ∑ j, w i j)/4 :=
    fun b => lt_of_not_ge (fun hb => h ⟨b,hb⟩)
  have hs := Finset.sum_lt_sum (s:=univ)
    (fun b _ => (h b).le) ⟨(fun _ => false),mem_univ _,h _⟩
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have he := sum_directedCutWeight w hdiag
  nlinarith only [hs,he]

end RegularPointCoordinates

end

end OAI
