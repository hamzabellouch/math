import OAI.NumberTheory.ShortEgyptian.WindowSpectrum

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem spectral_error_bound {q M : ℕ} [NeZero q] (hM : 3 * M ≤ q)
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (H : ℕ) (hH : 1 ≤ H) (eps : ℝ) (heps : 0 ≤ eps)
    (hFourier : ∀ k : ZMod q, k ≠ 0 → frequencyDistance k ≤ H →
      ‖probabilityFourier μ k‖ ≤ eps) :
    ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ‖charSum (natWindow q (3 * M)) k‖ * ‖charSum (natWindow q M) k‖ *
        ‖probabilityFourier μ k‖ ≤ 2 * eps * q * M + 2 * (q : ℝ) ^ 2 / H := by
  classical
  let a (k : ZMod q) := ‖charSum (natWindow q (3 * M)) k‖ * ‖charSum (natWindow q M) k‖
  have ha (k : ZMod q) : 0 ≤ a k := by dsimp [a]; positivity
  have hMq : M ≤ q := by omega
  have hl1 : (∑ k : ZMod q, a k) ≤ 2 * q * M := by
    have hh := charSum_l1_bound (natWindow q (3 * M)) (natWindow q M)
      (by rw [natWindow_card hM, natWindow_card hMq]; omega)
    simpa only [natWindow_card hMq] using hh
  have htail : (∑ k : ZMod q, if H < frequencyDistance k then a k else 0) ≤ 2 * (q : ℝ) ^ 2 / H := by
    rw [← Finset.sum_filter]
    exact window_spectral_tail hM hMq H hH
  have hterm (k : ZMod q) (hk : k ∈ (Finset.univ : Finset (ZMod q)).erase 0) :
      a k * ‖probabilityFourier μ k‖ ≤ eps * a k + if H < frequencyDistance k then a k else 0 := by
    by_cases hh : H < frequencyDistance k
    · rw [ite_eq_left hh]
      have hb := mul_le_mul_of_nonneg_left (probabilityFourier_norm μ hμ hmass k) (ha k)
      nlinarith [mul_nonneg heps (ha k)]
    · rw [ite_eq_right hh, add_zero]
      have hb := mul_le_mul_of_nonneg_left (hFourier k (Finset.mem_erase.mp hk).1 (by omega)) (ha k)
      simpa [mul_comm] using hb
  calc
    _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        (eps * a k + if H < frequencyDistance k then a k else 0) := Finset.sum_le_sum hterm
    _ ≤ ∑ k : ZMod q, (eps * a k + if H < frequencyDistance k then a k else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro k _ _
      positivity
    _ = eps * ∑ k : ZMod q, a k + ∑ k : ZMod q, if H < frequencyDistance k then a k else 0 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ eps * (2 * q * M) + 2 * (q : ℝ) ^ 2 / H :=
      add_le_add (mul_le_mul_of_nonneg_left hl1 heps) htail
    _ = _ := by ring

theorem window_mass_lower {q M : ℕ} [NeZero q] (hM : 1 ≤ M) (hMq : 3 * M ≤ q)
    (I : Finset (ZMod q)) (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hmass : ∑ x, μ x = 1)
    (hsupport : ∀ a ∈ natWindow q (3 * M), ∀ b ∈ natWindow q M, a + b ∈ I)
    (H : ℕ) (hH : 1 ≤ H) (eps : ℝ) (heps : 0 ≤ eps)
    (hFourier : ∀ k : ZMod q, k ≠ 0 → frequencyDistance k ≤ H →
      ‖probabilityFourier μ k‖ ≤ eps) :
    3 * M / (q : ℝ) - 2 * eps - 2 * q / ((M : ℝ) * H) ≤ ∑ x ∈ I, μ x := by
  have hMq' : M ≤ q := by omega
  have hc := convolution_discrepancy (natWindow q (3 * M)) (natWindow q M) I μ hμ hmass hsupport
  rw [natWindow_card hMq, natWindow_card hMq'] at hc
  push_cast at hc
  have he := spectral_error_bound hMq μ hμ hmass H hH eps heps hFourier
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hh : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  apply (mul_le_mul_iff_right₀ (mul_pos hq hm)).mp
  have halg : (q : ℝ) * M * (3 * M / (q : ℝ) - 2 * eps - 2 * q / ((M : ℝ) * H)) =
      3 * (M : ℝ) * M - 2 * eps * q * M - 2 * (q : ℝ) ^ 2 / H := by
    field_simp
  rw [halg]
  linarith

theorem charSum_norm_le_card {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (k : ZMod q) :
    ‖charSum A k‖ ≤ A.card := by
  calc
    _ ≤ ∑ a ∈ A, ‖ZMod.stdAddChar (k * a)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem uniform_mass_lower {q : ℕ} [NeZero q] (I : Finset (ZMod q))
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hFourier : ∀ k : ZMod q, k ≠ 0 → ‖probabilityFourier μ k‖ ≤ eps) :
    (I.card : ℝ) / q - I.card * eps ≤ ∑ x ∈ I, μ x := by
  classical
  have hc := convolution_discrepancy I {0} I μ hμ hmass
    (by intro a ha b hb; have hb0 : b = 0 := Finset.mem_singleton.mp hb; simpa [hb0] using ha)
  simp only [Finset.card_singleton, Nat.cast_one, mul_one, charSum, Finset.sum_singleton,
    mul_zero, AddChar.map_zero_eq_one, norm_one] at hc
  have he : (∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ‖charSum I k‖ * ‖probabilityFourier μ k‖) ≤ (q : ℝ) * I.card * eps := by
    calc
      _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, (I.card : ℝ) * eps := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul (charSum_norm_le_card I k) (hFourier k (Finset.mem_erase.mp hk).1)
          (norm_nonneg _) (by positivity)
      _ ≤ ∑ _k : ZMod q, (I.card : ℝ) * eps :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = _ := by simp [ZMod.card, nsmul_eq_mul, mul_assoc]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply (mul_le_mul_iff_right₀ hq).mp
  have halg : (q : ℝ) * ((I.card : ℝ) / q - I.card * eps) = I.card - q * I.card * eps := by
    field_simp
  rw [halg]
  change (I.card : ℝ) - (∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
    ‖charSum I k‖ * ‖probabilityFourier μ k‖) ≤ (q : ℝ) * ∑ x ∈ I, μ x at hc
  linarith

noncomputable def residueWindow (q : ℕ) (δ : ℝ) : Finset (ZMod q) :=
  natWindow q ⌈δ * q⌉₊

theorem residueWindow_size {q : ℕ} [NeZero q] {δ : ℝ} (hδ1 : δ ≤ 1) :
    (residueWindow q δ).card ≤ q ∧ δ * q ≤ ((residueWindow q δ).card : ℝ) := by
  have hceil : ⌈δ * (q : ℝ)⌉₊ ≤ q := Nat.ceil_le.mpr (by nlinarith [show (0 : ℝ) ≤ q by positivity])
  rw [residueWindow, natWindow_card hceil]
  exact ⟨hceil, Nat.le_ceil _⟩

theorem mem_residueWindow {q : ℕ} [NeZero q] {δ : ℝ} (hδ1 : δ ≤ 1) (x : ZMod q) :
    x ∈ residueWindow q δ ↔ (x.val : ℝ) < δ * q := by
  have hceil : ⌈δ * (q : ℝ)⌉₊ ≤ q := Nat.ceil_le.mpr (by nlinarith [show (0 : ℝ) ≤ q by positivity])
  constructor
  · intro hx
    obtain ⟨n, hn, hncast⟩ := Finset.mem_image.mp hx
    have hn' := Finset.mem_range.mp hn
    have hnv : (n : ZMod q).val = n := ZMod.val_natCast_of_lt (hn'.trans_le hceil)
    rw [← hncast, hnv]
    exact Nat.lt_ceil.mp hn'
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.val, Finset.mem_range.mpr (Nat.lt_ceil.mpr hx), ZMod.natCast_zmod_val x⟩

theorem finite_residue_discrepancy {q : ℕ} [NeZero q] (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256) (H : ℕ) (hH : 1 ≤ H)
    (hHδ : 1 ≤ 2 * (H : ℝ) * δ ^ 4)
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hFourier : ∀ k : ZMod q, k ≠ 0 → frequencyDistance k ≤ H →
      ‖probabilityFourier μ k‖ ≤ δ ^ 3) :
    δ / 2 ≤ ∑ x ∈ residueWindow q δ, μ x := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hh : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hδ1 : δ ≤ 1 := by linarith
  have hδsq : δ ^ 2 ≤ (1 / 256 : ℝ) ^ 2 := pow_le_pow_left₀ hδ.le hδsmall 2
  have hδcube : δ ^ 3 ≤ (1 / 256 : ℝ) ^ 3 := pow_le_pow_left₀ hδ.le hδsmall 3
  by_cases hlarge : 32 ≤ δ * q
  · let M : ℕ := ⌊δ * q / 4⌋₊
    have hMf : (M : ℝ) ≤ δ * q / 4 := Nat.floor_le (by positivity)
    have hMf' : δ * q / 4 < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    have hM0 : (0 : ℝ) < M := by linarith
    have hM : 1 ≤ M := by exact_mod_cast (show 0 < M from Nat.cast_pos.mp hM0)
    have hMq : 3 * M ≤ q := by
      have hh' : (3 : ℝ) * M ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hq.le]
      exact_mod_cast hh'
    have hMlo : δ * q / 8 ≤ (M : ℝ) := by linarith
    have hmean : 5 * δ / 8 ≤ 3 * M / (q : ℝ) := by
      apply (le_div_iff₀ hq).mpr
      nlinarith
    have hsupport : ∀ a ∈ natWindow q (3 * M), ∀ b ∈ natWindow q M,
        a + b ∈ residueWindow q δ := by
      intro a ha b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hij4 : i + j < 4 * M := by omega
      have hijδ : ((i + j : ℕ) : ℝ) < δ * q := by
        have hh' : ((i + j : ℕ) : ℝ) < 4 * M := by exact_mod_cast hij4
        linarith
      have hijq : i + j < q := by
        have hh' : ((i + j : ℕ) : ℝ) < q := hijδ.trans_le (by nlinarith [mul_le_mul_of_nonneg_right hδ1 hq.le])
        exact_mod_cast hh'
      apply (mem_residueWindow hδ1 _).mpr
      rw [← Nat.cast_add, ZMod.val_natCast_of_lt hijq]
      exact hijδ
    have hlower := window_mass_lower hM hMq (residueWindow q δ) μ hμ hmass hsupport
      H hH (δ ^ 3) (by positivity) hFourier
    have htail : 2 * (q : ℝ) / ((M : ℝ) * H) ≤ 32 * δ ^ 3 := by
      apply (div_le_iff₀ (mul_pos hM0 hh)).mpr
      calc
        _ ≤ 4 * (q : ℝ) * H * δ ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left hHδ (by positivity : (0 : ℝ) ≤ 2 * q)]
        _ = (32 * δ ^ 3 * H) * (δ * q / 8) := by ring
        _ ≤ (32 * δ ^ 3 * H) * M := mul_le_mul_of_nonneg_left hMlo (by positivity)
        _ = _ := by ring
    have herr : 34 * δ ^ 3 ≤ δ / 8 := by
      have hh' : 34 * δ ^ 2 ≤ 1 / 8 := by norm_num at hδsq ⊢; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh' hδ.le]
    linarith
  · have hqH : q ≤ H := by
      have hqH' : (q : ℝ) ≤ H := by
        apply (mul_le_mul_iff_left₀ (pow_pos hδ 4)).mp
        calc
          (q : ℝ) * δ ^ 4 = (δ * q) * δ ^ 3 := by ring
          _ ≤ 32 * δ ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ ≤ 1 / 2 := by norm_num at hδcube ⊢; nlinarith
          _ ≤ (H : ℝ) * δ ^ 4 := by linarith
      exact_mod_cast hqH'
    have hall (k : ZMod q) (hk : k ≠ 0) : ‖probabilityFourier μ k‖ ≤ δ ^ 3 := by
      apply hFourier k hk
      exact (min_le_left k.val (q - k.val)).trans ((ZMod.val_lt k).le.trans hqH)
    have hlower := uniform_mass_lower (residueWindow q δ) μ hμ hmass (δ ^ 3) (by positivity) hall
    obtain ⟨hcard, hcard'⟩ := residueWindow_size (q := q) hδ1
    have hmean : δ ≤ ((residueWindow q δ).card : ℝ) / q := (le_div_iff₀ hq).mpr hcard'
    have herr : ((residueWindow q δ).card : ℝ) * δ ^ 3 ≤ δ / 2 := by
      calc
        _ ≤ (q : ℝ) * δ ^ 3 := by gcongr
        _ = (δ * q) * δ ^ 2 := by ring
        _ ≤ 32 * δ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg δ)
        _ ≤ δ / 2 := by nlinarith [mul_le_mul_of_nonneg_left hδsmall hδ.le]
    linarith

end ShortEgyptian

end OAI
