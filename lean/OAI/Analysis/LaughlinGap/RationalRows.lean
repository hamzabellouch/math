import Mathlib
import OAI.Analysis.LaughlinGap.RationalCoupling

namespace OAI

/-! Rational Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

structure RationalRow where
  t : Fin 8
  lam : ℚ
  alpha : Fin 8 → Fin 9 → ℚ

noncomputable def rowNormalization (t p j : ℕ) : ℝ :=
  (Real.sqrt 2)^p * rootFactorial t * rootFactorial (p+j-t) /
    ((Real.sqrt 2)^t * rootFactorial p * rootFactorial j)

noncomputable def RationalRow.toReal (r : RationalRow) : RowData where
  t := r.t
  lam := r.lam
  alpha a := (r.alpha a.val.1 a.val.2 : ℝ) * rowNormalization r.t.val a.val.1.val a.val.2.val

noncomputable def threeRowScale (t z i : ℕ) : ℝ :=
  if z ≤ t+i then (Real.sqrt 2)^z * rootFactorial t * rootFactorial i /
    ((Real.sqrt 3)^(t+i)*(Real.sqrt 2)^t*rootFactorial z*rootFactorial (t+i-z)) else 0

def threeRowFactor (t z i : ℕ) : ℚ :=
  if z ≤ t+i then (2:ℚ)^z * t.factorial * i.factorial /
    ((3:ℚ)^(t+i)*(2:ℚ)^t*z.factorial*(t+i-z).factorial) else 0

lemma sqrt_natpow_sq {x : ℝ} (h : 0 ≤ x) (n : ℕ) : (Real.sqrt x ^ n)^2 = x^n := by
  rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt h]

lemma threeRowScale_sq (t z i : ℕ) : (threeRowScale t z i)^2 = (threeRowFactor t z i : ℝ) := by
  by_cases h : z ≤ t+i
  · simp only [threeRowScale,threeRowFactor,ite_eq_left h,div_pow,mul_pow,rootFactorial_sq,
      sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 2),sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 3)]
    push_cast
    rfl
  · simp [threeRowScale,threeRowFactor,h]

lemma rowNormalization_three {t : Fin 8} (a : RowEntry t) (z : ℕ) :
    rowNormalization t.val a.val.1.val a.val.2.val *
        threeWeightCoefficientStar z (t.val+a.output.val) a.val.1.val =
      (uCoefficient 2 z (t.val+a.output.val) a.val.1.val : ℝ) *
        threeRowScale t.val z a.output.val := by
  by_cases hz : z ≤ t.val+a.output.val
  · have he : t.val+a.output.val-a.val.1.val = a.val.2.val := by have := a.balance; omega
    rw [threeWeightCoefficientStar_rational hz,he,threeRowScale,ite_eq_left hz]
    dsimp [rowNormalization,RowEntry.output]
    field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]

  · simp [threeWeightCoefficientStar,hz,threeRowScale]

lemma threeWeight_row_t (t z i : ℕ) :
    threeWeightCoefficientStar z (t+i) t = (uCoefficient 2 z (t+i) t : ℝ) *
      threeRowScale t z i := by
  by_cases hz : z ≤ t+i
  · rw [threeWeightCoefficientStar_rational hz,threeRowScale,ite_eq_left hz,Nat.add_sub_cancel_left]
    ring
  · simp [threeWeightCoefficientStar,threeRowScale,hz]

lemma sum_fibers_multiply {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f : α → S) (g : β → S) :
    (∑ i, (∑ a, if o a=i then f a else 0)*g i) = ∑ a, f a*g (o a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma sum_fibers_trace {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f : α → S) (g : β → S) :
    (∑ a, f a*g (o a)) + (∑ a, ∑ b, if o a=o b then f a*f b else 0) =
      ∑ i, (∑ a, if o a=i then f a else 0)*((∑ a, if o a=i then f a else 0)+g i) := by
  rw [sum_fibers_multiply]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_ite,mul_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [eq_comm]

lemma rowTrace_regroup (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) (r : RowData) :
    rowTrace s z r = ∑ i : Fin 9,
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0)*
      ((∑ a : RowEntry r.t, if a.output=i then r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0) +
        2*r.lam*s z (r.t.val+i.val) r.t.val) := by
  classical
  have hf (i : Fin 9) : (∑ a : RowEntry r.t, if a.output=i then
      r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0) = ∑ a : RowEntry r.t,
        if a.output=i then r.alpha a*s z (r.t.val+a.output.val) a.val.1.val else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rw [h]
    · rfl
  simp_rw [hf]
  rw [← sum_fibers_trace]
  unfold rowTrace
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with h
    · rw [h]
      ring
    · rfl

def RationalRow.threeSum (r : RationalRow) (z : ℕ) (i : Fin 9) : ℚ :=
  ∑ a : RowEntry r.t, if a.output=i then
    r.alpha a.val.1 a.val.2 * uCoefficient 2 z (r.t.val+i.val) a.val.1.val else 0

def RationalRow.threeTrace (r : RationalRow) (z : ℕ) : ℚ :=
  ∑ i : Fin 9, threeRowFactor r.t.val z i.val * r.threeSum z i *
    (r.threeSum z i + 2*r.lam*uCoefficient 2 z (r.t.val+i.val) r.t.val)

lemma RationalRow.threeSum_normalized (r : RationalRow) (z : ℕ) (i : Fin 9) :
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) =
      (r.threeSum z i : ℝ) * threeRowScale r.t.val z i.val := by
  unfold RationalRow.threeSum
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a.output=i
  · simp only [ite_eq_left h,RationalRow.toReal]
    rw [mul_assoc,← h,rowNormalization_three]
    push_cast
    ring
  · simp [h]

lemma RationalRow.threeTrace_eq (r : RationalRow) (z : ℕ) :
    rowTrace threeWeightCoefficientStar z r.toReal = (r.threeTrace z : ℝ) := by
  rw [rowTrace_regroup]
  simp only [RationalRow.toReal]
  change (∑ i : Fin 9, (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
    threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) *
      ((∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
    threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) +
      2*(r.lam:ℝ)*threeWeightCoefficientStar z (r.t.val+i.val) r.t.val)) = _
  simp_rw [r.threeSum_normalized,threeWeight_row_t]
  simp only [RationalRow.threeTrace,Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← threeRowScale_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
