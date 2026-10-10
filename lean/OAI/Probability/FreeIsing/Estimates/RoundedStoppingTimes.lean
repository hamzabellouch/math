import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.RoundedStoppingTimes

def round (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈t * (n + 1 : ℝ≥0)⌉₊ : ℝ≥0) / (n + 1 : ℝ≥0)

private theorem mesh_pos (n : ℕ) : (0 : ℝ≥0) < n + 1 := by positivity

theorem le_round (n : ℕ) (t : ℝ≥0) : t ≤ round n t := by
  rw [round, le_div_iff₀ (mesh_pos n)]
  exact Nat.le_ceil _

theorem round_le_add (n : ℕ) (t : ℝ≥0) :
    round n t ≤ t + 1 / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), add_mul,
    div_mul_cancel₀ _ (ne_of_gt (mesh_pos n))]
  exact (Nat.ceil_lt_add_one zero_le).le

theorem round_le_iff (n : ℕ) (s t : ℝ≥0) :
    round n s ≤ t ↔ s ≤ (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), ← Nat.le_floor_iff zero_le,
    Nat.ceil_le, le_div_iff₀ (mesh_pos n)]

theorem floor_div_le (n : ℕ) (t : ℝ≥0) :
    (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) ≤ t := by
  rw [div_le_iff₀ (mesh_pos n)]
  exact Nat.floor_le zero_le

theorem tendsto_round (t : ℝ≥0) : Tendsto (fun n => round n t) atTop (𝓝 t) := by
  have hu : Tendsto (fun n : ℕ => t + 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_round n t) (fun n => round_le_add n t)

def roundTop (n : ℕ) : WithTop ℝ≥0 → WithTop ℝ≥0 := WithTop.map (round n)

@[simp] theorem roundTop_top (n : ℕ) : roundTop n ⊤ = ⊤ := rfl

@[simp] theorem roundTop_coe (n : ℕ) (t : ℝ≥0) :
    roundTop n t = (round n t : WithTop ℝ≥0) := rfl

theorem le_roundTop (n : ℕ) (t : WithTop ℝ≥0) : t ≤ roundTop n t := by
  cases t with
  | top => simp
  | coe t => simpa only [roundTop_coe, WithTop.coe_le_coe] using le_round n t

theorem roundTop_le_iff (n : ℕ) (s : WithTop ℝ≥0) (t : ℝ≥0) :
    roundTop n s ≤ t ↔
      s ≤ (((⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) := by
  cases s with
  | top => simp only [roundTop_top, WithTop.top_le_iff, WithTop.coe_ne_top]
  | coe s => simpa only [roundTop_coe, WithTop.coe_le_coe] using round_le_iff n s t

theorem countable_range_roundTop (n : ℕ) : (Set.range (roundTop n)).Countable := by
  refine ((Set.countable_range (fun k : ℕ =>
    ((k : ℝ≥0) / (n + 1 : ℝ≥0) : WithTop ℝ≥0))).insert ⊤).mono ?_
  rintro _ ⟨t, rfl⟩
  cases t with
  | top => exact Set.mem_insert _ _
  | coe t =>
    exact Set.mem_insert_of_mem _ ⟨⌈t * (n + 1 : ℝ≥0)⌉₊, rfl⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {F : Filtration ℝ≥0 m}

theorem isStoppingTime_roundTop {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (n : ℕ) : IsStoppingTime F (fun ω => roundTop n (τ ω)) := by
  intro t
  simp only [roundTop_le_iff]
  exact F.mono (floor_div_le n t) _ (hτ _)

theorem countable_range_roundTop_comp (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => roundTop n (τ ω))).Countable :=
  (countable_range_roundTop n).mono (Set.range_comp_subset_range _ _)

theorem tendsto_min_roundTop_untopA (t : ℝ≥0) (s : WithTop ℝ≥0) :
    Tendsto (fun n => (min (t : WithTop ℝ≥0) (roundTop n s)).untopA)
      atTop (𝓝 (min (t : WithTop ℝ≥0) s).untopA) := by
  cases s with
  | top => simp
  | coe s =>
    simpa only [roundTop_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe] using
      (tendsto_const_nhds.min (tendsto_round s) :
        Tendsto (fun n => min t (round n s)) atTop (𝓝 (min t s)))

theorem exists_countable_range_approximation {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    ∃ τn : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsStoppingTime F (τn n)) ∧
      (∀ n, (Set.range (τn n)).Countable) ∧
      (∀ (ω : Ω) (t : ℝ≥0), Tendsto (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA)
        atTop (𝓝 (min (t : WithTop ℝ≥0) (τ ω)).untopA)) := by
  exact ⟨fun n ω => roundTop n (τ ω), isStoppingTime_roundTop hτ,
    countable_range_roundTop_comp τ, fun ω t => tendsto_min_roundTop_untopA t (τ ω)⟩

end Problem367.RoundedStoppingTimes

end

end OAI
