import Mathlib
import OAI.Computability.MinUncut.Estimates.Density
import OAI.Computability.MinUncut.Estimates.Convolution

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
local instance maskRowKernelDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def maskRowKernel (active : Bool) (b c : W) : ℝ :=
  if active then rowDensity 0 b c-1 else 1

omit [AddCommGroup W] [Module F₂ W] in
lemma maskRowKernel_symmetric (active : Bool) (b c : W) :
    maskRowKernel active b c = maskRowKernel active c b := by
  simp only [maskRowKernel, rowDensity_symmetric]

omit [Module F₂ W] in
lemma maskRowKernel_abs_mean (active : Bool) (b : W) :
    (𝔼 c, |maskRowKernel active b c|) ≤ if active then 2 else 1 := by
  cases active
  · simp [maskRowKernel]
  · dsimp only [maskRowKernel]
    calc
      _ ≤ 𝔼 c, (rowDensity 0 b c+1) := by
        apply Finset.expect_le_expect
        intro c _
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (rowDensity_nonneg (by norm_num) (by norm_num) _ _), abs_one])
      _ = 2 := by rw [Finset.expect_add_distrib, rowDensity_mean]; norm_num

lemma maskRowKernel_character (active : Bool) (b : W) (α : Module.Dual F₂ W) :
    (𝔼 c, maskRowKernel active b c * character α c) =
      if active = decide (α ≠ 0) then character α b else 0 := by
  cases active
  · simp [maskRowKernel, character_mean]
    split_ifs with h
    · simp [h]
    · rfl
  · simp only [maskRowKernel, ↓reduceIte, sub_mul, one_mul,
      Finset.expect_sub_distrib, row_character_eigen, character_mean]
    by_cases h : α=0 <;> simp [h]

def maskKernel (S : Finset R) (B C : R → W) : ℝ :=
  ∏ r, maskRowKernel (decide (r ∈ S)) (B r) (C r)

omit [AddCommGroup W] [Module F₂ W] in
lemma maskKernel_symmetric (S : Finset R) (B C : R → W) :
    maskKernel S B C = maskKernel S C B := by simp only [maskKernel, maskRowKernel_symmetric]

omit [Module F₂ W] in
lemma maskKernel_abs_mean (S : Finset R) (B : R → W) :
    (𝔼 C, |maskKernel S B C|) ≤ (2 : ℝ)^Fintype.card R := by
  simp only [maskKernel, Finset.abs_prod]
  rw [expect_prod (f := fun r (c : W) => |maskRowKernel (decide (r ∈ S)) (B r) c|)]
  calc
    _ ≤ ∏ r : R, (2:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro r _; exact Finset.expect_nonneg (fun _ _ => abs_nonneg _)
      · intro r _
        exact (maskRowKernel_abs_mean _ _).trans (by split_ifs <;> norm_num)
    _ = _ := by simp

lemma maskKernel_character (S : Finset R) (B : R → W) (α : Module.Dual F₂ (R → W)) :
    (𝔼 C, maskKernel S B C * character α C) = if mask α=S then character α B else 0 := by
  simp only [maskKernel, character_product, ← Finset.prod_mul_distrib]
  rw [expect_prod (f := fun r (c : W) => maskRowKernel (decide (r ∈ S)) (B r) c * character (frequency α r) c)]
  simp only [maskRowKernel_character]
  have he (r : R) : (decide (r ∈ S) = decide (frequency α r ≠ 0)) ↔
      (r ∈ S ↔ r ∈ mask α) := by
    by_cases h₁ : r ∈ S <;> by_cases h₂ : frequency α r=0 <;> simp [mask, h₁, h₂]
  by_cases hs : mask α=S
  · rw [ite_eq_left hs]
    apply Finset.prod_congr rfl
    intro r _
    rw [ite_eq_left ((he r).mpr (by rw [hs]))]
  · rw [ite_eq_right hs]
    have hh : ∃ r, ¬(r ∈ S ↔ r ∈ mask α) := by
      by_contra hn
      push Not at hn
      exact hs (Finset.ext (fun r => (hn r).symm))
    obtain ⟨r,hr⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right (fun h => hr ((he r).mp h)))

def maskProject (S : Finset R) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  𝔼 C, maskKernel S B C * f C

lemma maskProject_expansion (S : Finset R) (f : (R → W) → ℝ) (B : R → W) :
    maskProject S f B = ∑ α : Module.Dual F₂ (R → W),
      if mask α=S then coefficient f α * character α B else 0 := by
  unfold maskProject
  conv_lhs => arg 2; ext C; rw [← inversion f C]
  simp only [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [mul_left_comm _ (coefficient f α), ← Finset.mul_expect, maskKernel_character]
  split_ifs <;> simp

lemma coefficient_maskProject (S : Finset R) (f : (R → W) → ℝ) (α : Module.Dual F₂ (R → W)) :
    coefficient (maskProject S f) α = if mask α=S then coefficient f α else 0 := by
  have he (B : R → W) : maskProject S f B =
      ∑ β ∈ Finset.univ.filter (fun β : Module.Dual F₂ (R → W) => mask β=S), coefficient f β*character β B := by
    rw [maskProject_expansion, Finset.sum_filter]
  unfold coefficient
  simp_rw [he, Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect,
    character_orthogonality]
  simp [Finset.mem_filter, coefficient]

omit [Module F₂ W] in
lemma maskProject_l1 (S : Finset R) (f : (R → W) → ℝ) :
    (𝔼 B, |maskProject S f B|) ≤ (2:ℝ)^Fintype.card R * (𝔼 B, |f B|) := by
  calc
    _ ≤ 𝔼 B, 𝔼 C, |maskKernel S B C| * |f C| := by
      apply Finset.expect_le_expect
      intro B _
      simpa only [maskProject, abs_mul] using Finset.abs_expect_le Finset.univ (fun C => maskKernel S B C*f C)
    _ = 𝔼 C, (𝔼 B, |maskKernel S C B|)*|f C| := by
      rw [Finset.expect_comm]
      simp only [maskKernel_symmetric, Finset.expect_mul]
    _ ≤ 𝔼 C, (2:ℝ)^Fintype.card R * |f C| := by
      apply Finset.expect_le_expect
      intro C _
      exact mul_le_mul_of_nonneg_right (maskKernel_abs_mean S C) (abs_nonneg _)
    _ = _ := (Finset.mul_expect _ _ _).symm
end MinUncut.RowNoise

end

end OAI
