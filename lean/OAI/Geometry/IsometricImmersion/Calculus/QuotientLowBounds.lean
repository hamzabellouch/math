import OAI.Geometry.IsometricImmersion.Calculus.QuotientLowRecurrence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

def bound0 (M c : ℝ) : ℝ := M / c
def bound1 (M c : ℝ) : ℝ := (M + M * bound0 M c) / c
def bound2 (M c : ℝ) : ℝ := (M + M * bound0 M c + 2 * M * bound1 M c) / c
def bound3 (M c : ℝ) : ℝ :=
  (M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c) / c
def boundThroughThree (M c : ℝ) : ℝ := bound0 M c + bound1 M c + bound2 M c + bound3 M c

theorem bounds_nonneg {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    0 ≤ bound0 M c ∧ 0 ≤ bound1 M c ∧ 0 ≤ bound2 M c ∧ 0 ≤ bound3 M c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [bound0, bound1, bound2, bound3] <;> positivity

private theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

private theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) (hA : 0 ≤ A) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hA

private theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub x y).trans (add_le_add hx hy)

theorem abs_div_bound {x y N c : ℝ} (hN : 0 ≤ N) (hnum : |x| ≤ N)
    (hc : 0 < c) (hden : c ≤ |y|) : |x / y| ≤ N / c := by
  rw [abs_div]
  exact div_le_div₀ hN hnum hc hden

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem denominator_ne_zero (hc : 0 < c) (hden : ∀ p ∈ U, c ≤ |b p|) :
    ∀ p ∈ U, b p ≠ 0 := by
  intro p hp hzero
  have hh := hden p hp
  rw [hzero, abs_zero] at hh
  linarith

theorem quotient_bound_zero (hM : 0 ≤ M) (hc : 0 < c)
    (ha0 : ∀ p ∈ U, |a p| ≤ M) (hden : ∀ p ∈ U, c ≤ |b p|)
    {p : Coord} (hp : p ∈ U) : |a p / b p| ≤ bound0 M c :=
  abs_div_bound hM (ha0 p hp) hc (hden p hp)

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

theorem quotient_bound_one {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    |iteratedCoordPartial [i] (fun x => a x / b x) p| ≤ bound1 M c := by
  rw [quotient_one ha hb hU hp (denominator_ne_zero hc hden) i]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  apply abs_div_bound (by have := (bounds_nonneg hM hc).1; positivity) _ hc (hden p hp)
  exact abs_sub_bound (haB [i] (by norm_num) p hp)
    (abs_mul_bound (hbB [i] (by norm_num) p hp) hq0 hM)

theorem quotient_bound_two {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (fun x => a x / b x) p| ≤ bound2 M c := by
  rw [quotient_two ha hb hU hp (denominator_ne_zero hc hden) i j]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hterm0 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hq0 hM
  have htermi := abs_mul_bound (hbB [j] (by norm_num) p hp) hqi hM
  have htermj := abs_mul_bound (hbB [i] (by norm_num) p hp) hqj hM
  have hrest := abs_add_bound (abs_add_bound hterm0 htermi) htermj
  have hnum := abs_sub_bound (haB [i, j] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 2 * M * bound1 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_three {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (fun x => a x / b x) p| ≤ bound3 M c := by
  rw [quotient_three ha hb hU hp (denominator_ne_zero hc hden) i j k]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hqk := quotient_bound_one ha hb hU hM hc haB hbB hden hp k
  have hqij := quotient_bound_two ha hb hU hM hc haB hbB hden hp i j
  have hqik := quotient_bound_two ha hb hU hM hc haB hbB hden hp i k
  have hqjk := quotient_bound_two ha hb hU hM hc haB hbB hden hp j k
  have h0 := abs_mul_bound (hbB [i, j, k] (by norm_num) p hp) hq0 hM
  have h1 := abs_mul_bound (hbB [j, k] (by norm_num) p hp) hqi hM
  have h2 := abs_mul_bound (hbB [i, k] (by norm_num) p hp) hqj hM
  have h3 := abs_mul_bound (hbB [k] (by norm_num) p hp) hqij hM
  have h4 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hqk hM
  have h5 := abs_mul_bound (hbB [j] (by norm_num) p hp) hqik hM
  have h6 := abs_mul_bound (hbB [i] (by norm_num) p hp) hqjk hM
  have hrest := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
    (abs_add_bound (abs_add_bound h0 h1) h2) h3) h4) h5) h6
  have hnum := abs_sub_bound (haB [i, j, k] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_through_three (ds : List (Fin 2)) (hlen : ds.length ≤ 3)
    {p : Coord} (hp : p ∈ U) :
    |iteratedCoordPartial ds (fun x => a x / b x) p| ≤ boundThroughThree M c := by
  obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc
  have hB0 : bound0 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB1 : bound1 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB2 : bound2 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB3 : bound3 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  cases ds with
  | nil => exact (quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp).trans hB0
  | cons i ds =>
    cases ds with
    | nil => exact (quotient_bound_one ha hb hU hM hc haB hbB hden hp i).trans hB1
    | cons j ds =>
      cases ds with
      | nil => exact (quotient_bound_two ha hb hU hM hc haB hbB hden hp i j).trans hB2
      | cons k ds =>
        cases ds with
        | nil => exact (quotient_bound_three ha hb hU hM hc haB hbB hden hp i j k).trans hB3
        | cons l ds => simp only [List.length_cons] at hlen; omega

end SmoothQuotient
end SmoothLocal.Geometry.LowQuotient

end

end OAI
