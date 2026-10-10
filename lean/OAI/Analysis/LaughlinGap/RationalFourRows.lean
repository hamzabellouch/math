import Mathlib
import OAI.Analysis.LaughlinGap.RationalFourCoefficients
import OAI.Analysis.LaughlinGap.RationalRows

namespace OAI

/-! Rational Four Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

noncomputable def fourRowScale (t D i k : ℕ) : ℝ :=
  if D ≤ t+i+k then rootFactorial t * rootFactorial i * rootFactorial k /
    ((2:ℝ)^(t+i+k)*Real.sqrt 2^t*rootFactorial (t+i+k-D)) else 0

def fourRowFactor (t D i k : ℕ) : ℚ :=
  if D ≤ t+i+k then (t.factorial * i.factorial * k.factorial : ℚ) /
    ((2:ℚ)^(2*(t+i+k)+t)*(t+i+k-D).factorial) else 0

lemma fourRowScale_swap (t D i k : ℕ) : fourRowScale t D i k = fourRowScale t D k i := by
  have he : t+i+k=t+k+i := by omega
  simp only [fourRowScale,he]
  split_ifs <;> ring

lemma fourRowScale_sq (t D i k : ℕ) : (fourRowScale t D i k)^2 = (fourRowFactor t D i k : ℝ) := by
  by_cases h : D ≤ t+i+k
  · simp only [fourRowScale,fourRowFactor,ite_eq_left h,div_pow,mul_pow,rootFactorial_sq,
      sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    rw [← pow_mul,← pow_add]
    simp only [Nat.mul_comm]
  · simp [fourRowScale,fourRowFactor,h]

lemma rowNormalization_four {t : Fin 8} (a : RowEntry t) {D r : ℕ}
    (hr : r ≤ D) (ho : Odd r) (k : ℕ) :
    rowNormalization t.val a.val.1.val a.val.2.val *
        fourWeightCoefficientStar D (t.val+a.output.val+k) r a.val.1.val a.val.2.val k =
      ((vCoefficient D (t.val+a.output.val+k) r a.val.1.val a.val.2.val k *
        (2:ℚ)^((r+1)/2+a.val.1.val) : ℚ) : ℝ) * copyNormalization D r *
        fourRowScale t.val D a.output.val k := by
  by_cases hD : D ≤ t.val+a.output.val+k
  · rw [fourWeightCoefficientStar_rational hr ho,fourRowScale,ite_eq_left hD]
    dsimp [rowNormalization,RowEntry.output]
    push_cast
    have ht : (Real.sqrt 2 ^ a.val.1.val)^2 = (2:ℝ)^a.val.1.val := sqrt_natpow_sq (by norm_num) _
    field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
    linear_combination (vCoefficient D (t.val+(a.val.1.val+a.val.2.val-t.val)+k)
      r a.val.1.val a.val.2.val k : ℝ) * (2:ℝ)^((r+1)/2) * copyNormalization D r * ht
  · simp [fourWeightCoefficientStar,vCoefficient,fourRowScale,hD]

lemma sum_fibers_cross {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f g : α → β → S) :
    (∑ i, ∑ k, (∑ a, if o a=i then f a k else 0) *
      (∑ b, if o b=k then g b i else 0)) = ∑ a, ∑ b, f a (o b)*g b (o a) := by
  calc
    _ = ∑ i, ∑ b, g b i*(∑ a, if o a=i then f a (o b) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [mul_comm] using sum_fibers_multiply o (fun b => g b i)
        (fun k => ∑ a, if o a=i then f a k else 0)
    _ = ∑ b, ∑ i, (∑ a, if o a=i then f a (o b) else 0)*g b i := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = ∑ b, ∑ a, f a (o b)*g b (o a) := by
      simp only [sum_fibers_multiply]
    _ = _ := Finset.sum_comm

lemma rowFourMatrix_regroup (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ)
    (D : ℕ) (r : RowData) (u v : FourCopy D) :
    rowFourMatrix s D r u v = -(∑ i : Fin 9, ∑ k : Fin 9,
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+i.val+k.val) u.val.val a.val.1.val a.val.2.val k.val else 0) *
      (∑ b : RowEntry r.t, if b.output=k then r.alpha b *
        s D (r.t.val+i.val+k.val) v.val.val b.val.1.val b.val.2.val i.val else 0)) := by
  classical
  have hf (i k : Fin 9) (w : FourCopy D) :
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+i.val+k.val) w.val.val a.val.1.val a.val.2.val k.val else 0) =
      ∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+a.output.val+k.val) w.val.val a.val.1.val a.val.2.val k.val else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rw [h]
    · rfl
  have hk (i k : Fin 9) : r.t.val+i.val+k.val=r.t.val+k.val+i.val := by omega
  conv_rhs => arg 1; arg 2; ext i; arg 2; ext k; arg 2; rw [hk i k]
  simp_rw [hf]
  rw [sum_fibers_cross]
  unfold rowFourMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [a.balance]
  have he : r.t.val+b.output.val+a.output.val=a.val.1.val+a.val.2.val+b.output.val := by
    have := a.balance; omega
  rw [he]
  ring

def RationalRow.fourSum (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ a : RowEntry r.t, if a.output=i then r.alpha a.val.1 a.val.2 *
    vCoefficient D (r.t.val+i.val+k.val) s a.val.1.val a.val.2.val k.val *
      (2:ℚ)^((s+1)/2+a.val.1.val) else 0

def RationalRow.fourMatrix (r : RationalRow) (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℚ :=
  fun u v => -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSum D u.val.val i k * r.fourSum D v.val.val k i)

lemma RationalRow.fourSum_normalized (r : RationalRow) (D : ℕ) (s : FourCopy D) (i k : Fin 9) :
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) s.val.val a.val.1.val a.val.2.val k.val else 0) =
      (r.fourSum D s.val.val i k : ℝ) * copyNormalization D s.val.val *
        fourRowScale r.t.val D i.val k.val := by
  unfold RationalRow.fourSum
  push_cast
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a.output=i
  · simp only [ite_eq_left h,RationalRow.toReal]
    rw [mul_assoc,← h,rowNormalization_four a (Nat.le_of_lt_succ s.val.isLt) s.property]
    push_cast
    ring
  · simp [h]

lemma RationalRow.fourMatrix_eq (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    rowFourMatrix fourWeightCoefficientStar D r.toReal u v =
      copyNormalization D u.val.val * (r.fourMatrix D u v : ℝ) * copyNormalization D v.val.val := by
  rw [rowFourMatrix_regroup]
  change -(∑ i : Fin 9, ∑ k : Fin 9,
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) u.val.val a.val.1.val a.val.2.val k.val else 0) *
    (∑ b : RowEntry r.t, if b.output=k then r.toReal.alpha b *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) v.val.val b.val.1.val b.val.2.val i.val else 0)) = _
  have he (i k : Fin 9) : r.t.val+i.val+k.val=r.t.val+k.val+i.val := by omega
  conv_lhs => arg 1; arg 2; ext i; arg 2; ext k; arg 2; rw [he i k]
  simp only [RationalRow.fourSum_normalized]
  simp only [RationalRow.fourMatrix,Rat.cast_neg,Rat.cast_sum,Rat.cast_mul]
  simp only [mul_neg,neg_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourRowScale_swap r.t.val D k.val i.val,← fourRowScale_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
