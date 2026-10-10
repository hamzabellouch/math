import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! # A polynomial-size coordinate mesh for a bounded parameter cube -/

noncomputable section

namespace PolycyclicRecognition

theorem exists_coordinate_mesh (n : ℕ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * R / ρ + 2 ∧
      ∃ c : (Fin n → Fin k) → (Fin n → ℝ),
        (∀ i, ‖c i‖ ≤ R + ρ) ∧
        ∀ x : Fin n → ℝ, ‖x‖ ≤ R → ∃ i, dist x (c i) ≤ ρ := by
  let k := ⌈2 * R / ρ⌉₊ + 1
  have hratio : 0 ≤ 2 * R / ρ := div_nonneg (by positivity) hρ.le
  have hk : (k : ℝ) ≤ 2 * R / ρ + 2 := by
    dsimp only [k]
    have h := Nat.ceil_lt_add_one hratio
    push_cast
    linarith
  let c := fun i : Fin n → Fin k => fun j => -R + ρ * (i j : ℕ)
  refine ⟨k, hk, c, ?_, ?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R + ρ)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have hji : (i j : ℕ) ≤ ⌈2 * R / ρ⌉₊ := Nat.le_of_lt_succ (i j).isLt
    have hj : ((i j : ℕ) : ℝ) ≤ (⌈2 * R / ρ⌉₊ : ℝ) := by exact_mod_cast hji
    have hc := Nat.ceil_lt_add_one hratio
    have hp : ρ * ((i j : ℕ) : ℝ) ≤ 2 * R + ρ := by
      have ht := mul_le_mul_of_nonneg_left (hj.trans hc.le) hρ.le
      have he : ρ * (2 * R / ρ + 1) = 2 * R + ρ := by field_simp
      rwa [he] at ht
    dsimp only [c]
    constructor
    · nlinarith [show (0 : ℝ) ≤ ((i j : ℕ) : ℝ) from Nat.cast_nonneg _]
    · linarith
  · intro x hx
    have hxj := (pi_norm_le_iff_of_nonneg hR).mp hx
    let i : Fin n → Fin k := fun j => ⟨⌊(x j + R) / ρ⌋₊, by
      have hj : (x j + R) / ρ ≤ 2 * R / ρ := by
        apply div_le_div_of_nonneg_right _ hρ.le
        have := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).2
        linarith
      exact Nat.lt_succ_of_le ((Nat.floor_mono hj).trans (Nat.floor_le_ceil _))⟩
    refine ⟨i, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
    intro j
    have hlow : -R ≤ x j := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).1
    have hnonneg : 0 ≤ (x j + R) / ρ := div_nonneg (by linarith) hρ.le
    have hlo := (le_div_iff₀ hρ).mp (Nat.floor_le hnonneg)
    have hhi := (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one ((x j + R) / ρ))
    change ‖x j - (-R + ρ * (⌊(x j + R) / ρ⌋₊ : ℝ))‖ ≤ ρ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end PolycyclicRecognition

end

end OAI
