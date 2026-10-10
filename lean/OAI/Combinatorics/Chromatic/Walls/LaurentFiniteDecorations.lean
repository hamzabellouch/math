import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RootProducts

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section

def multiplicity (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) : ℕ:=(h j).choose
lemma multiplicity_cast (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) :
    (multiplicity w h j:ℚ)=w.coeff j:=(h j).choose_spec.symm
lemma coeff_nonneg (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) : 0≤w.coeff j:=by
  rw [←multiplicity_cast w h j]
  exact Nat.cast_nonneg _

lemma coeff_mul_natCast (w:LaurentSeries ℚ) (k:ℕ) (j:ℤ) :
    (w*k).coeff j=w.coeff j*k := by
  calc
    _ = (k • w).coeff j:=by rw [nsmul_eq_mul,mul_comm]
    _ = k • w.coeff j:=congrFun HahnSeries.coeff_nsmul j
    _ = _:=by simp only [nsmul_eq_mul,mul_comm]

lemma support_of_positive_sum {L:Type*} [Fintype L] (w:L → LaurentSeries ℚ)
    (hw:∀l,Positive (w l)) (c:L → ℕ) (hc:∀l,0<c l)
    (P:ℤ → Prop) (H:∀j,¬P j → (∑l,w l*c l).coeff j=0) :
    ∀l j,(w l).coeff j≠0 → P j := by
  intro l j hj
  by_contra hn
  have Hz:=H j hn
  rw [HahnSeries.coeff_sum] at Hz
  simp only [coeff_mul_natCast] at Hz
  have hnon:∀i,0≤(w i).coeff j*(c i:ℚ):=fun i=>mul_nonneg (coeff_nonneg _ (hw i) j) (Nat.cast_nonneg _)
  have hle:=Finset.single_le_sum (f:=fun i=>(w i).coeff j*(c i:ℚ))
    (fun i _=>hnon i) (Finset.mem_univ l)
  rw [Hz] at hle
  have hp:0<(w l).coeff j:=lt_of_le_of_ne (coeff_nonneg _ (hw l) j) (Ne.symm hj)
  have hcp:0<(c l:ℚ):=Nat.cast_pos.mpr (hc l)
  exact (not_lt_of_ge hle) (mul_pos hp hcp)

lemma exponent_injective (M:ℕ) : Function.Injective (fun k:Fin (M+1)=>(M:ℤ)-2*(k.val:ℤ)) := by
  intro k l h
  change (M:ℤ)-2*(k.val:ℤ)=(M:ℤ)-2*(l.val:ℤ) at h
  apply Fin.ext
  omega

lemma finite_expansion (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ)
    (hs:∀j,w.coeff j≠0 → ∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)) :
    w=∑k:Fin (M+1),HahnSeries.single ((M:ℤ)-2*k.val)
      (multiplicity w hw ((M:ℤ)-2*k.val):ℚ) := by
  ext j
  rw [HahnSeries.coeff_sum]
  by_cases he:∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)
  · obtain ⟨k,rfl⟩:=he
    rw [Finset.sum_eq_single k]
    · rw [HahnSeries.coeff_single,ite_eq_left rfl,multiplicity_cast]
    · intro l hl hlk
      exact HahnSeries.coeff_single_of_ne (fun H=>hlk ((exponent_injective M) H.symm))
    · simp
  · rw [not_exists] at he
    have hz:w.coeff j=0:=by
      by_contra hn
      obtain ⟨k,hk⟩:=hs j hn
      exact he k hk
    rw [hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    exact HahnSeries.coeff_single_of_ne (he k)

abbrev Decoration (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ) :=
  Σk:Fin (M+1),Fin (multiplicity w hw ((M:ℤ)-2*k.val))

lemma decoration_expansion (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ)
    (hs:∀j,w.coeff j≠0 → ∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)) :
    w=∑d:Decoration w hw M,(↑(LaurentRay.vUnit^(2*(d.1.val:ℤ)-(M:ℤ))):LaurentSeries ℚ) := by
  calc
    w = ∑k:Fin (M+1),HahnSeries.single ((M:ℤ)-2*k.val)
      (multiplicity w hw ((M:ℤ)-2*k.val):ℚ) := finite_expansion w hw M hs
    _ = _ := ?_
  unfold Decoration
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [LaurentRay.vUnit_zpow,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  have he:-(2*(k.val:ℤ)-(M:ℤ))=(M:ℤ)-2*k.val:=by omega
  rw [he]
  ext j
  simp only [HahnSeries.coeff_nsmul,HahnSeries.coeff_single]
  by_cases hj:j=(M:ℤ)-2*k.val <;> simp [hj,nsmul_eq_mul]
end
end ElementaryPositivity.LaurentPositive

end

end OAI
