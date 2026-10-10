import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.Preliminaries.SeparatedSetSquares

namespace OAI

/-! # The cubic detector kernel on separated ordinates -/

namespace Ostmann

open scoped BigOperators

noncomputable def densityCubicWeight (u : ℝ) : ℝ := 1 / (1 + |u|) ^ 3

 theorem densityCubicWeight_nonneg (u : ℝ) : 0 ≤ densityCubicWeight u := by
  unfold densityCubicWeight
  positivity

 theorem densityCubicWeight_le_one (u : ℝ) : densityCubicWeight u ≤ 1 := by
  unfold densityCubicWeight
  apply (div_le_one (by positivity)).mpr
  nlinarith [abs_nonneg u, sq_nonneg |u|]

 theorem densityCubicWeight_le_inverse_square (u : ℝ) (hu : u ≠ 0) :
    densityCubicWeight u ≤ 1 / u ^ 2 := by
  unfold densityCubicWeight
  apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hu)
  have he : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rw [he]
  nlinarith [abs_nonneg u, sq_nonneg |u|]

 theorem densityCubicWeight_rpow (u : ℝ) :
    densityCubicWeight u = (1 + |u|) ^ (-(3 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  simp [densityCubicWeight]

 theorem densityCubicWeight_separated_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (v : ℝ) :
    (∑ x ∈ S, densityCubicWeight (v - x)) ≤ 1 + 4 * Real.pi ^ 2 / 3 := by
  classical
  let A := S.filter (fun x => |v - x| < 1 / 2)
  let B := S.filter (fun x => ¬ |v - x| < 1 / 2)
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hd := hsep x hx'.1 y hy'.1 hxy
    have ht : |x - y| ≤ |v - x| + |v - y| := by
      calc
        _ = |(v - y) - (v - x)| := by congr 1; ring
        _ ≤ |v - y| + |v - x| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (v - y) (-(v - x))
        _ = _ := by ring
    linarith
  have hnear : (∑ x ∈ A, densityCubicWeight (v - x)) ≤ 1 := by
    calc
      _ ≤ ∑ _x ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun x _ => densityCubicWeight_le_one (v - x))
      _ = (A.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hA
  let R := B.image (fun x => v - x)
  have hinj : Function.Injective (fun x : ℝ => v - x) := by
    intro x y h
    linarith
  have hRfirst : ∀ x ∈ R, (1 / 2 : ℝ) ≤ |x| := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact le_of_not_gt (Finset.mem_filter.mp hy).2
  have hRsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → (1 / 2 : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg (fun z => v - z) h)
    have h := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    have he : |(v - a) - (v - b)| = |a - b| := by
      rw [show (v - a) - (v - b) = -(a - b) by ring, abs_neg]
    rw [he]
    linarith
  have hfar := separated_set_inverse_squares R (1 / 2) (by norm_num) hRfirst hRsep
  have hsumR : (∑ x ∈ B, 1 / (v - x) ^ 2) = ∑ x ∈ R, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    exact fun x _ y _ h => hinj h
  have hB : (∑ x ∈ B, densityCubicWeight (v - x)) ≤ 4 * Real.pi ^ 2 / 3 := by
    calc
      _ ≤ ∑ x ∈ B, 1 / (v - x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply densityCubicWeight_le_inverse_square
        intro he
        have h := (Finset.mem_filter.mp hx).2
        simp only [he, abs_zero] at h
        norm_num at h
      _ = ∑ x ∈ R, 1 / x ^ 2 := hsumR
      _ ≤ Real.pi ^ 2 / (3 * (1 / 2) ^ 2) := hfar
      _ = _ := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun x => |v - x| < 1 / 2) (fun x => densityCubicWeight (v - x))
  change (∑ x ∈ A, densityCubicWeight (v - x)) +
    (∑ x ∈ B, densityCubicWeight (v - x)) = _ at hsplit
  linarith

end Ostmann

end OAI
