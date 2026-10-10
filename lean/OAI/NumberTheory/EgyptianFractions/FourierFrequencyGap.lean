import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Nontrivial cancellation at all prescribed low frequencies forces the
modulus itself to lie beyond that range. -/
theorem modulus_gt_low_frequency_range {q : ℕ} [NeZero q]
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (x : ι → ZMod q)
    (H : ℕ) (ε : ℝ) (hε : ε < 1)
    (hfourier : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
      ‖(∑ i ∈ I, ZMod.stdAddChar ((ℓ : ZMod q) * x i)) / (I.card : ℂ)‖ ≤ ε) :
    H < q := by
  by_contra h
  have hqH : q ≤ H := by omega
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h := hfourier q hq1 hqH
  have hcard : I.card ≠ 0 := ne_of_gt (Finset.card_pos.mpr hI)
  have hcardC : (I.card : ℂ) ≠ 0 := by exact_mod_cast hcard
  simp only [ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_self hcardC, norm_one] at h
  linarith

/-- The frequency range needed for localization also guarantees that the
cyclic interval contains many integer representatives. -/
theorem low_frequency_gap_scale (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hgap : ⌊1 / δ ^ 4⌋₊ < q) : 128 ≤ δ * q := by
  have hq : 1 / δ ^ 4 < (q : ℝ) := (Nat.floor_lt (by positivity)).mp hgap
  have hδ8 : δ ≤ (1 / 8 : ℝ) := by linarith
  have hcube : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by gcongr
  have hbound : (128 : ℝ) ≤ δ * (1 / δ ^ 4) := by
    have heq : δ * (1 / δ ^ 4) = 1 / δ ^ 3 := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < δ ^ 3)).mpr
    norm_num at hcube
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left hq.le hδ.le)

/-- Conjugating all phases does not change the normalized Fourier modulus. -/
theorem negative_character_average_norm {G ι : Type*} [Finite G] [AddCommGroup G]
    (ψ : AddChar G ℂ) (I : Finset ι) (x : ι → G) :
    ‖(∑ i ∈ I, ψ (-x i)) / (I.card : ℂ)‖ =
      ‖(∑ i ∈ I, ψ (x i)) / (I.card : ℂ)‖ := by
  calc
    _ = ‖(starRingEnd ℂ) ((∑ i ∈ I, ψ (x i)) / (I.card : ℂ))‖ := by
      simp [map_div₀, map_sum, AddChar.map_neg_eq_conj]
    _ = _ := Complex.norm_conj _

/-- Positive-frequency bounds control every off-diagonal difference in a
short geometric kernel. -/
theorem difference_frequency_average_bound {q : ℕ} [NeZero q]
    {ι : Type*} (I : Finset ι) (x : ι → ZMod q) (H : ℕ) (ε : ℝ)
    (hfourier : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
      ‖(∑ i ∈ I, ZMod.stdAddChar ((ℓ : ZMod q) * x i)) / (I.card : ℂ)‖ ≤ ε)
    (a b : ℕ) (ha : a ≤ H) (hb : b ≤ H) (hab : a ≠ b) :
    ‖(∑ i ∈ I, ZMod.stdAddChar (((a : ZMod q) - (b : ZMod q)) * x i)) / (I.card : ℂ)‖ ≤ ε := by
  by_cases hba : b ≤ a
  · have hdiff := hfourier (a - b) (by omega) (by omega)
    simpa only [Nat.cast_sub hba] using hdiff
  · have hab' : a ≤ b := by omega
    have hdiff := hfourier (b - a) (by omega) (by omega)
    have heq : (a : ZMod q) - (b : ZMod q) = -((b - a : ℕ) : ZMod q) := by
      rw [Nat.cast_sub hab']
      ring
    rw [heq]
    simp_rw [neg_mul]
    rw [negative_character_average_norm]
    exact hdiff

end Problem337

end

end OAI
