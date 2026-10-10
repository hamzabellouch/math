import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Filter
open scoped Topology

def descentExponent (r : ℕ) : ℝ := ((r : ℝ)+2)/((r : ℝ)+1)

theorem descentExponent_eq (r : ℕ) : descentExponent r = 1+1/((r:ℝ)+1) := by
  unfold descentExponent
  field_simp
  ring

@[simp] theorem descentExponent_zero : descentExponent 0 = 2 := by norm_num [descentExponent]

theorem one_lt_descentExponent (r : ℕ) : 1 < descentExponent r := by
  rw [descentExponent_eq]
  have : 0 < 1/((r:ℝ)+1) := by positivity
  linarith

theorem descentExponent_le_two (r : ℕ) : descentExponent r ≤ 2 := by
  rw [descentExponent_eq]
  have : 1/((r:ℝ)+1) ≤ (1:ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  linarith

theorem descentExponent_succ (r : ℕ) :
    descentExponent (r+1) = 2-1/descentExponent r := by
  unfold descentExponent
  push_cast
  field_simp
  ring

theorem descentExponent_tendsto : Tendsto descentExponent atTop (𝓝 (1:ℝ)) := by
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun r : ℕ => (1:ℝ)/((r:ℝ)+1)) atTop (𝓝 0))
  simpa only [add_zero,← descentExponent_eq] using hh

theorem exists_descentExponent_le {ε : ℝ} (hε : 0 < ε) :
    ∃ r, descentExponent r ≤ 1+ε := by
  have he := descentExponent_tendsto.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1+ε))
  obtain ⟨r,hr⟩ := he.exists
  exact ⟨r,hr.le⟩

theorem property_at_descentExponent (P : ℝ → Prop) (hinit : P 2)
    (himprove : ∀ ξ, 1 < ξ → ξ ≤ 2 → P ξ → P (2-1/ξ)) :
    ∀ r, P (descentExponent r) := by
  intro r
  induction r with
  | zero => simpa using hinit
  | succ r ih =>
    rw [descentExponent_succ]
    exact himprove _ (one_lt_descentExponent r) (descentExponent_le_two r) ih

end Ostmann.QuadraticSieve

end

end OAI
