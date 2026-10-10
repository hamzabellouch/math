import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- The natural remainder specified by a ceiling step is the canonical
representative of the negative residue, including remainder zero. -/
theorem residue_eq_neg_zmod_val {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) : h = (-(N : ZMod u)).val := by
  have hzmod := congrArg (fun a : ℕ => (a : ZMod u)) heq
  simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_mul] at hzmod
  have hcast : (h : ZMod u) = -(N : ZMod u) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hzmod.symm
  rw [← hcast, ZMod.val_natCast_of_lt hh]

/-- The same remainder normalized by its modulus is the real fractional part. -/
theorem residue_div_eq_fract_neg {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) :
    (h : ℝ) / u = Int.fract (-(N : ℝ) / u) := by
  have hu : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  apply Eq.symm
  apply Int.fract_eq_iff.mpr
  refine ⟨by positivity, (div_lt_one hu).mpr (by exact_mod_cast hh), -(z : ℤ), ?_⟩
  have heqR : (u : ℝ) * z = N + h := by exact_mod_cast heq
  push_cast
  rw [← sub_div]
  apply (div_eq_iff (ne_of_gt hu)).2
  nlinarith

/-- Arithmetic specifications of the nonnegative ceiling remainder. -/
theorem natural_ceil_residue_spec (u N : ℕ) (hu : 0 < u) :
    N ≤ u * ⌈(N : ℝ) / u⌉₊ ∧
    u * ⌈(N : ℝ) / u⌉₊ = N + (u * ⌈(N : ℝ) / u⌉₊ - N) ∧
    u * ⌈(N : ℝ) / u⌉₊ - N < u := by
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hlo : (N : ℝ) / u ≤ (⌈(N : ℝ) / u⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈(N : ℝ) / u⌉₊ : ℝ) < (N : ℝ) / u + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hN : N ≤ u * ⌈(N : ℝ) / u⌉₊ := by
    have h := (div_le_iff₀ huR).mp hlo
    exact_mod_cast (show (N : ℝ) ≤ (u : ℝ) * (⌈(N : ℝ) / u⌉₊ : ℝ) by nlinarith)
  have hNu : u * ⌈(N : ℝ) / u⌉₊ < N + u := by
    have hmul := mul_lt_mul_of_pos_right hhi huR
    have hcancel : (N : ℝ) / u * u = N := div_mul_cancel₀ _ (ne_of_gt huR)
    exact_mod_cast (show (u : ℝ) * (⌈(N : ℝ) / u⌉₊ : ℝ) < (N : ℝ) + u by nlinarith)
  exact ⟨hN, by omega, by omega⟩

theorem natural_ceil_residue_eq_neg_zmod_val (u N : ℕ) (hu : 0 < u) :
    u * ⌈(N : ℝ) / u⌉₊ - N = (-(N : ZMod u)).val := by
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u N hu
  exact residue_eq_neg_zmod_val hlt heq

theorem natural_ceil_residue_div_eq_fract_neg (u N : ℕ) (hu : 0 < u) :
    ((u * ⌈(N : ℝ) / u⌉₊ - N : ℕ) : ℝ) / u = Int.fract (-(N : ℝ) / u) := by
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u N hu
  exact residue_div_eq_fract_neg hlt heq


/-- Exact conversion of a real residue cutoff to the fractional-part interval. -/
theorem residue_lt_iff_fract_lt {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) (δ : ℝ) :
    (h : ℝ) < δ * u ↔ Int.fract (-(N : ℝ) / u) < δ := by
  have hu : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  rw [← residue_div_eq_fract_neg hh heq]
  exact (div_lt_iff₀ hu).symm

/-- Exact conversion to the normalized canonical representative in `ZMod`. -/
theorem residue_lt_iff_neg_zmod_val_lt {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) (δ : ℝ) :
    (h : ℝ) < δ * u ↔ ((-(N : ZMod u)).val : ℝ) / u < δ := by
  have hu : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  rw [← residue_eq_neg_zmod_val hh heq]
  exact (div_lt_iff₀ hu).symm

end Problem337

end

end OAI
