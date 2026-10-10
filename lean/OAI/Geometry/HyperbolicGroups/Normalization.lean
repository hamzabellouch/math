import Mathlib
import OAI.Geometry.HyperbolicGroups.GeometricAction
import OAI.Geometry.HyperbolicGroups.Moment

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

@[ext] lemma ext {μ ν : FiniteLaw α} (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

/-- Normalization of nonnegative counts. Positivity is proved before this
construction is used to form the uniform present-star law. -/
def normalize (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hz : 0 < ∑ a, f a) : FiniteLaw α where
  mass a := f a / ∑ a, f a
  nonneg a := div_nonneg (hf a) hz.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hz)

lemma abs_sum_sub_const (f : α → ℝ) (c : ℝ) :
    |(∑ a, f a) - Fintype.card α * c| ≤ ∑ a, |f a - c| := by
  simpa [Finset.sum_sub_distrib] using Finset.abs_sum_le_sum_abs (fun a => f a - c) Finset.univ

/-- The exact deterministic normalization estimate
for branch fibers and for ordered-distinct leaf fibers. -/
theorem normalize_uniform_bound [Nonempty α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hz : 0 < ∑ a, f a) (c : ℝ) :
    (normalize f hf hz).totalVariation uniform ≤ (∑ a, |f a - c|) / ∑ a, f a := by
  let Z : ℝ := ∑ a, f a
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := α)
  have hZ : 0 < Z := hz
  have hpoint (a : α) : |f a / Z - 1 / n| ≤ |f a - c| / Z + |c / Z - 1 / n| := by
    calc
      _ = |(f a - c) / Z + (c / Z - 1 / n)| := by congr 1; ring
      _ ≤ |(f a - c) / Z| + |c / Z - 1 / n| := abs_add_le _ _
      _ = _ := by rw [abs_div,abs_of_pos hZ]
  have hc : n * |c / Z - 1 / n| = |Z - n * c| / Z := by
    have he : n * (c / Z - 1 / n) = -(Z - n * c) / Z := by field_simp; ring
    calc
      _ = |n * (c / Z - 1 / n)| := by rw [abs_mul,abs_of_pos hn]
      _ = _ := by rw [he,abs_div,abs_of_pos hZ,abs_neg]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  rw [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change (∑ a, |f a / Z - 1 / n|) ≤ (∑ a, |f a - c|) / Z + n * |c / Z - 1 / n| at hs
  rw [hc] at hs
  have he := (div_le_div_of_nonneg_right (abs_sum_sub_const f c) hZ.le)
  change |Z - n * c| / Z ≤ (∑ a, |f a - c|) / Z at he
  unfold totalVariation normalize uniform
  change (∑ a, |f a / Z - 1 / n|) / 2 ≤ _
  linarith

lemma totalVariation_triangle (μ ν κ : FiniteLaw α) :
    μ.totalVariation κ ≤ μ.totalVariation ν + ν.totalVariation κ := by
  unfold totalVariation
  rw [← add_div,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum fun a _ => abs_sub_le _ _ _

lemma totalVariation_map_le (μ ν : FiniteLaw α) (f : α → β) :
    (μ.map f).totalVariation (ν.map f) ≤ μ.totalVariation ν := by
  classical
  unfold totalVariation map
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b, ∑ a, |(if f a = b then μ.mass a else 0) - (if f a = b then ν.mass a else 0)| := by
      exact Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp

lemma map_map {γ : Type*} [Fintype γ] (μ : FiniteLaw α) (f : α → β) (g : β → γ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  classical
  apply FiniteLaw.ext
  funext c
  unfold map
  simp only
  have hi (b : β) : (if g b = c then ∑ a, if f a = b then μ.mass a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then μ.mass a else 0) else 0 := by
    by_cases h : g b = c <;> simp [h]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hj (b : β) : (if g b = c then (if f a = b then μ.mass a else 0) else 0) =
      (if f a = b then (if g (f a) = c then μ.mass a else 0) else 0) := by
    by_cases h : f a = b
    · subst b; simp
    · simp [h]
  simp_rw [hj]
  simp

lemma expect_abs_sub_le_relative (μ : FiniteLaw α) (f : α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ μ.expect f) (hv : μ.variance f ≤ r * μ.expect f ^ 2) :
    μ.expect (fun a => |f a - μ.expect f|) ≤ Real.sqrt r * μ.expect f := by
  calc
    _ ≤ Real.sqrt (μ.variance f) := μ.expect_abs_sub_le f
    _ ≤ Real.sqrt (r * μ.expect f ^ 2) := Real.sqrt_le_sqrt hv
    _ = _ := by rw [Real.sqrt_mul hr,Real.sqrt_sq hm]

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
