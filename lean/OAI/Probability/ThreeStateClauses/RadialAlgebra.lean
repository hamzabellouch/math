import Mathlib

namespace OAI

/-! Radial Algebra. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
namespace ThreeState.TreeClauses.Radial

abbrev Vec := Fin 3 → ℝ

def avg (w : Vec) : ℝ := (w 0 + w 1 + w 2) / 3

def PositiveMessage (m : Vec) : Prop := (∀ i, 0 < m i) ∧ avg m = 1

def centered (m : Vec) : Vec := fun i ↦ m i - 1

def momentX (v : Vec) : ℝ := avg (fun i ↦ v i ^ 2) / 2

def momentY (v : Vec) : ℝ := avg (fun i ↦ v i ^ 3) / 2

def logAverage (m : Vec) : ℝ := avg (fun i ↦ Real.log (m i))

def logCentered (m : Vec) : Vec := fun i ↦ Real.log (m i) - logAverage m

def info (m : Vec) : ℝ := avg (fun i ↦ m i * Real.log (m i))

def symEntropy (m : Vec) : ℝ := avg (fun i ↦ (m i - 1) * Real.log (m i)) / 2

def correction (m : Vec) : ℝ := avg (fun i ↦ m i * logCentered m i ^ 2) / 2

def functional (m : Vec) : ℝ := 3 * info m - 2 * symEntropy m + (4 / 5) * correction m

def edge (t : ℝ) (m : Vec) : Vec := fun i ↦ 1 + t * (m i - 1)

def RadialInequality : Prop := ∀ (m : Vec), PositiveMessage m → ∀ (lam : ℝ),
  0 < lam → lam < 1 →
  (1 - lam ^ 2) / 2 * momentX (centered m) ^ 2 ≤
    functional m - (lam ^ 2)⁻¹ * functional (edge lam m)

lemma avg_add (v w : Vec) : avg (fun i ↦ v i + w i) = avg v + avg w := by
  simp only [avg]; ring

lemma avg_sub (v w : Vec) : avg (fun i ↦ v i - w i) = avg v - avg w := by
  simp only [avg]; ring

lemma avg_mul (a : ℝ) (v : Vec) : avg (fun i ↦ a * v i) = a * avg v := by
  simp only [avg]; ring

lemma avg_const (a : ℝ) : avg (fun _ ↦ a) = a := by simp only [avg]; ring

lemma avg_centered {m : Vec} (hm : PositiveMessage m) : avg (centered m) = 0 := by
  have h := hm.2
  dsimp [centered, avg] at *
  linarith

lemma info_eq (m : Vec) : info m = logAverage m + 2 * symEntropy m := by
  simp only [info, logAverage, symEntropy, avg]; ring

lemma functional_eq (m : Vec) :
    functional m = 3 * logAverage m + 4 * symEntropy m + (4 / 5) * correction m := by
  rw [functional, info_eq]; ring

lemma third_eq {v : Vec} (hv : avg v = 0) : v 2 = -v 0 - v 1 := by
  simp only [avg] at hv; linarith

lemma momentX_nonneg (v : Vec) : 0 ≤ momentX v := by
  unfold momentX avg; positivity

lemma cubic {v : Vec} (hv : avg v = 0) (i : Fin 3) :
    v i ^ 3 = 3 * momentX v * v i + 2 * momentY v := by
  have hc := third_eq hv
  fin_cases i
  · change v 0 ^ 3 = 3 * momentX v * v 0 + 2 * momentY v
    simp only [momentX, momentY, avg]; rw [hc]; ring
  · change v 1 ^ 3 = 3 * momentX v * v 1 + 2 * momentY v
    simp only [momentX, momentY, avg]; rw [hc]; ring
  · change v 2 ^ 3 = 3 * momentX v * v 2 + 2 * momentY v
    simp only [momentX, momentY, avg]; rw [hc]; ring

lemma product_eq {v : Vec} (hv : avg v = 0) (t : ℝ) :
    (1 + t * v 0) * (1 + t * v 1) * (1 + t * v 2) =
      1 - 3 * t ^ 2 * momentX v + 2 * t ^ 3 * momentY v := by
  simp only [momentX, momentY, avg]; rw [third_eq hv]; ring

lemma discriminant {v : Vec} (hv : avg v = 0) :
    (v 0 - v 1) ^ 2 * (v 0 - v 2) ^ 2 * (v 1 - v 2) ^ 2 =
      108 * (momentX v ^ 3 - momentY v ^ 2) := by
  simp only [momentX, momentY, avg]; rw [third_eq hv]; ring

lemma moment_discriminant {v : Vec} (hv : avg v = 0) :
    momentY v ^ 2 ≤ momentX v ^ 3 := by
  have h : 0 ≤ (v 0 - v 1) ^ 2 * (v 0 - v 2) ^ 2 * (v 1 - v 2) ^ 2 := by positivity
  rw [discriminant hv] at h; linarith

lemma momentX_lt_one {m : Vec} (hm : PositiveMessage m) : momentX (centered m) < 1 := by
  have hs : m 0 + m 1 + m 2 = 3 := by simpa only [avg, div_eq_iff (by norm_num : (3:ℝ) ≠ 0), one_mul] using hm.2
  have h01 := mul_pos (hm.1 0) (hm.1 1)
  have h02 := mul_pos (hm.1 0) (hm.1 2)
  have h12 := mul_pos (hm.1 1) (hm.1 2)
  dsimp [momentX, avg, centered]
  nlinarith [sq_nonneg (m 0 + m 1 + m 2 - 3)]

lemma denominator_pos {m : Vec} (hm : PositiveMessage m) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - 3 * t ^ 2 * momentX (centered m) + 2 * t ^ 3 * momentY (centered m) := by
  rw [← product_eq (avg_centered hm)]
  have hi (i : Fin 3) : 0 < 1 + t * centered m i := by
    dsimp [centered]
    by_cases h : t = 0
    · subst t; norm_num
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
      have := mul_pos ht0 (hm.1 i)
      nlinarith [ht.2]
  exact mul_pos (mul_pos (hi 0) (hi 1)) (hi 2)

def hpoly (v : Vec) : Vec := fun i ↦ 1 - v i + v i ^ 2 - 3 * momentX v

def Hpoly (j : ℕ) (v : Vec) : ℝ := avg (fun i ↦ hpoly v i ^ j)

lemma Hpoly_one {v : Vec} (hv : avg v = 0) : Hpoly 1 v = 1 - momentX v := by
  simp only [Hpoly, hpoly, momentX, avg, pow_one]; rw [third_eq hv]; ring

lemma Hpoly_two {v : Vec} (hv : avg v = 0) :
    Hpoly 2 v = 3 * momentX v ^ 2 - 4 * momentY v + 1 := by
  simp only [Hpoly, hpoly, momentX, momentY, avg]; rw [third_eq hv]; ring

lemma Hpoly_three {v : Vec} (hv : avg v = 0) :
    Hpoly 3 v = -9 * momentX v ^ 3 + 9 * momentX v ^ 2 +
      6 * momentX v * momentY v + 3 * momentX v + 4 * momentY v ^ 2 - 14 * momentY v + 1 := by
  simp only [Hpoly, hpoly, momentX, momentY, avg]; rw [third_eq hv]; ring

def polyA (x y : ℝ) : ℝ :=
  3*x^4 + 12*x^3 + x^2 + (-6*x^3 - 28*x^2 - 2*x)*y + (26*x - 2)*y^2 - 4*y^3

def polyC (x y : ℝ) : ℝ :=
  6*x^4 - 2*x^3 + (-13*x^3 - 10*x^2 - x)*y + (10*x^2 + 22*x + 4)*y^2 - 16*y^3

def polyN (x y t : ℝ) : ℝ := (24/5) * (polyA x y + t * polyC x y)

def polyL (x y : ℝ) : ℝ :=
  1500*x^5 - 1020*x^4 + 240*x^3 + 168*y^4 +
  (-480*x^2 - 756*x - 52)*y^3 +
  (2114*x^3 + 710*x^2 + 48*x - 80)*y^2 +
  (-3093*x^4 + 736*x^3 - 35*x^2)*y

lemma polyN_one (x y : ℝ) :
    polyN x y 1 = (24/5) * (x-y) * (9*x-10*y+1) * (x^2+x-2*y) := by
  simp only [polyN, polyA, polyC]; ring

lemma polyN_affine (x y t : ℝ) :
    polyN x y t = (1-t)*polyN x y 0 + t*polyN x y 1 := by
  simp only [polyN]; ring

end ThreeState.TreeClauses.Radial

end

end OAI
