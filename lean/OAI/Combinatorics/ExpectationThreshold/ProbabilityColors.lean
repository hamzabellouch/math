import OAI.Combinatorics.ExpectationThreshold.ProbabilityProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

abbrev Color (s : ℕ) := Fin (s + 1)

abbrev Coloring (α : Type*) (s : ℕ) := α → Color s

/-- The geometric sum appearing in the admissibility condition. -/
def scaleSum (s : ℕ) : ℝ := ∑ i : Fin s, (256 : ℝ) ^ (i.val + 1)

/-- The literal single-coordinate probabilities from the selector experiment. -/
def colorProb (p : ℝ) (s : ℕ) (c : Color s) : ℝ :=
  if c.val < s then (256 : ℝ) ^ (c.val + 1) * p else 1 - p * scaleSum s

@[simp] theorem scaleSum_zero : scaleSum 0 = 0 := by
  simp [scaleSum]

theorem scaleSum_nonneg (s : ℕ) : 0 ≤ scaleSum s := by
  exact Finset.sum_nonneg fun i _ => pow_nonneg (by norm_num) _

@[simp] theorem colorProb_castSucc (p : ℝ) (s : ℕ) (i : Fin s) :
    colorProb p s i.castSucc = (256 : ℝ) ^ (i.val + 1) * p := by
  simp [colorProb, i.isLt]

@[simp] theorem colorProb_last (p : ℝ) (s : ℕ) :
    colorProb p s (Fin.last s) = 1 - p * scaleSum s := by
  simp [colorProb]

/-- Normalization is an algebraic identity, even before assuming positivity. -/
theorem sum_colorProb (p : ℝ) (s : ℕ) : ∑ c : Color s, colorProb p s c = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [colorProb_castSucc, colorProb_last]
  rw [← Finset.sum_mul]
  change scaleSum s * p + (1 - p * scaleSum s) = 1
  ring

theorem colorProb_pos (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) : 0 < colorProb p s c := by
  unfold colorProb
  split_ifs
  · exact mul_pos (pow_pos (by norm_num) _) hp
  · linarith

theorem colorProb_nonneg (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) : 0 ≤ colorProb p s c :=
  (colorProb_pos p s hp hs c).le

theorem colorProb_le_one (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) : colorProb p s c ≤ 1 := by
  rw [← sum_colorProb p s]
  exact Finset.single_le_sum (fun d _ => colorProb_nonneg p s hp hs d)
    (Finset.mem_univ c)

def colorLaw (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) : FiniteLaw (Color s) where
  weight := colorProb p s
  nonneg := colorProb_nonneg p s hp hs
  total := sum_colorProb p s

@[simp] theorem colorLaw_weight (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) :
    (colorLaw p s hp hs).weight c = colorProb p s c := rfl

theorem colorLaw_isPositive (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) : (colorLaw p s hp hs).IsPositive :=
  colorProb_pos p s hp hs

variable {α : Type*} [Fintype α]

/-- Probability mass of a complete coloring, with one factor per vertex. -/
def colorMass (p : ℝ) (s : ℕ) (a : Coloring α s) : ℝ :=
  ∏ x, colorProb p s (a x)

theorem colorMass_pos (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 < colorMass p s a := by
  exact Finset.prod_pos fun x _ => colorProb_pos p s hp hs (a x)

theorem colorMass_nonneg (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 ≤ colorMass p s a :=
  (colorMass_pos p s hp hs a).le

variable [DecidableEq α]

/-- Summing over actual colorings gives total mass one. -/
theorem sum_colorMass (p : ℝ) (s : ℕ) :
    ∑ a : Coloring α s, colorMass p s a = 1 := by
  classical
  unfold colorMass
  rw [← Fintype.prod_sum (fun (_ : α) (c : Color s) => colorProb p s c)]
  simp only [sum_colorProb, Finset.prod_const_one]

/-- The independent product law on exactly the original vertex set. -/
def coloringLaw (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) : FiniteLaw (Coloring α s) :=
  FiniteLaw.pi (fun _ : α => colorLaw p s hp hs)

@[simp] theorem coloringLaw_weight (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) :
    (coloringLaw p s hp hs).weight a = colorMass p s a := rfl

theorem coloringLaw_isPositive (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) :
    (coloringLaw (α := α) p s hp hs).IsPositive :=
  colorMass_pos p s hp hs

/-- Coordinate observables have the explicitly specified color marginal. -/
theorem coloringLaw_expectation_coordinate (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (x : α) (f : Color s → ℝ) :
    (coloringLaw p s hp hs).expectation (fun a => f (a x)) =
      ∑ c : Color s, colorProb p s c * f c :=
  FiniteLaw.expectation_pi_coordinate (fun _ : α => colorLaw p s hp hs) x f

/-- Independent coordinate observables factor under the actual coloring law. -/
theorem coloringLaw_expectation_product (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (f : α → Color s → ℝ) :
    (coloringLaw p s hp hs).expectation (fun a => ∏ x, f x (a x)) =
      ∏ x, ∑ c : Color s, colorProb p s c * f x c :=
  FiniteLaw.expectation_pi_product (fun _ : α => colorLaw p s hp hs) f

end TalagrandThreshold

end

end OAI
