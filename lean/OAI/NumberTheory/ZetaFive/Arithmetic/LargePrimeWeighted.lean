import OAI.NumberTheory.ZetaFive.Arithmetic.LargePrimeIntegral
import OAI.NumberTheory.ZetaFive.Identities.Endpoints
import OAI.NumberTheory.ZetaFive.Identities.RiemannSqueeze

namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def affineGrid (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (b - a) / n * i

noncomputable def affineLower (a b m c D : ℝ) (n i : ℕ) : ℝ :=
  m * affineGrid a b n i + c - if i = n - 1 then D else 0

noncomputable def affineUpper (a b m c D : ℝ) (n i : ℕ) : ℝ :=
  m * affineGrid a b n (i + 1) + c + if i = n - 1 then D else 0

theorem grid_zero (a b : ℝ) (n : ℕ) : affineGrid a b n 0 = a := by
  simp [affineGrid]

theorem grid_end (a b : ℝ) {n : ℕ} (hn : 0 < n) : affineGrid a b n n = b := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold affineGrid
  rw [div_mul_cancel₀ _ hn']
  ring

theorem grid_width (a b : ℝ) (n i : ℕ) :
    affineGrid a b n (i + 1) - affineGrid a b n i = (b - a) / n := by
  simp only [affineGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem grid_strict {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (affineGrid a b n) := by
  intro i j hij
  unfold affineGrid
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_left (by exact_mod_cast hij)
      (div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)))

theorem affine_cell_envelopes {F : ℝ → ℝ} {a b m c D : ℝ}
    (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    {n : ℕ} (hn : 0 < n) :
    ∀ i < n, ∀ x ∈ Set.Ioc (affineGrid a b n i) (affineGrid a b n (i + 1)),
      affineLower a b m c D n i ≤ F x ∧ F x ≤ affineUpper a b m c D n i := by
  intro i hi x hx
  have hg := grid_strict hab hn
  have hxlo : a < x := by
    have h := hg.monotone (Nat.zero_le i)
    rw [grid_zero] at h
    exact h.trans_lt hx.1
  have hxhi : x ≤ b := by
    have h := hg.monotone (show i + 1 ≤ n by omega)
    rw [grid_end a b hn] at h
    exact hx.2.trans h
  have hcorr : 0 ≤ (if i = n - 1 then D else 0) := by split_ifs <;> positivity
  by_cases hxb : x < b
  · rw [hpiece x hxlo hxb]
    unfold affineLower affineUpper
    constructor
    · have h := mul_le_mul_of_nonneg_left hx.1.le hm
      linarith
    · have h := mul_le_mul_of_nonneg_left hx.2 hm
      linarith
  · have heq : x = b := le_antisymm hxhi (le_of_not_gt hxb)
    have hiend : i = n - 1 := by
      by_contra hne
      have hin : i + 1 < n := by omega
      have hglt := hg hin
      rw [grid_end a b hn] at hglt
      exact (not_lt_of_ge (heq ▸ hx.2)) hglt
    have hright : affineGrid a b n (i + 1) = b := by
      have hin : i + 1 = n := by omega
      rw [hin, grid_end a b hn]
    have hmlo := mul_le_mul_of_nonneg_left hx.1.le hm
    have he := abs_le.mp hend
    subst x
    simp only [affineLower, affineUpper, ite_eq_left hiend, hright]
    constructor <;> linarith

theorem affine_envelope_gap (a b m c D : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
      ((affineUpper a b m c D n i - affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i))) =
      (m * (b - a) ^ 2 + 2 * D * (b - a)) / n := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlast : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  simp only [grid_width]
  have heq : ∀ i : ℕ,
      (affineUpper a b m c D n i - affineLower a b m c D n i) * ((b - a) / n) =
        m * ((b - a) / n) ^ 2 + (if i = n - 1 then 2 * D * ((b - a) / n) else 0) := by
    intro i
    unfold affineUpper affineLower affineGrid
    simp only [Nat.cast_add, Nat.cast_one]
    split_ifs <;> ring
  simp_rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite_eq', ite_eq_left hlast]
  field_simp [hn']

theorem affine_envelope_balance (a b m c D : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
      ((affineUpper a b m c D n i + affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i))) =
      2 * (m * (b ^ 2 - a ^ 2) / 2 + c * (b - a)) := by
  let P : ℝ → ℝ := fun x => m * x ^ 2 / 2 + c * x
  have heq : ∀ i : ℕ,
      (affineUpper a b m c D n i + affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i) =
      2 * (P (affineGrid a b n (i + 1)) - P (affineGrid a b n i)) := by
    intro i
    dsimp [affineUpper, affineLower, P]
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum,
    Finset.sum_range_sub (fun i => P (affineGrid a b n i)) n,
    grid_end a b hn, grid_zero]
  dsimp [P]
  ring

theorem affine_piece_darboux {F : ℝ → ℝ} {a b m c D : ℝ}
    (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    (hIntegral : (∫ x in a..b, F x) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a)) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (p l u : ℕ → ℝ),
      Monotone p ∧ p 0 = a ∧ p n = b ∧
      (∀ i < n, p i < p (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in a..b, F x) - ε < ∑ i ∈ Finset.range n, l i * (p (i + 1) - p i) ∧
      (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) < (∫ x in a..b, F x) + ε := by
  intro ε hε
  let K := m * (b - a) ^ 2 + 2 * D * (b - a)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (K / ε))
  have hn0 : 0 < n := by
    have h : (0 : ℝ) < n := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hn)
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgap : K / n < ε := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (le_max_right (1 : ℝ) (K / ε)).trans_lt hn
    have h' := (div_lt_iff₀ hε).mp h
    nlinarith
  refine ⟨n, affineGrid a b n, affineLower a b m c D n,
    affineUpper a b m c D n, (grid_strict hab hn0).monotone,
    grid_zero a b n, grid_end a b hn0, ?_,
    affine_cell_envelopes hab hm hD hpiece hend hn0, ?_, ?_⟩
  · intro i _
    exact grid_strict hab hn0 (Nat.lt_succ_self i)
  · have hg := affine_envelope_gap a b m c D hn0
    have hb := affine_envelope_balance a b m c D hn0
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hg hb
    rw [hIntegral]
    dsimp [K] at hgap
    linarith
  · have hg := affine_envelope_gap a b m c D hn0
    have hb := affine_envelope_balance a b m c D hn0
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hg hb
    rw [hIntegral]
    dsimp [K] at hgap
    linarith

theorem weighted_affine_piece_tendsto {F : ℝ → ℝ} {a b m c D : ℝ}
    (ha : 0 < a) (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    (hIntegral : (∫ x in a..b, F x) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a))
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) := by
  exact weightedPrimeIntervalSum_tendsto_of_darboux ha hab hPNT
    (affine_piece_darboux hab hm hD hpiece hend hIntegral)

theorem largePrime_weighted_piece_01
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (9) (46 / 5))
      atTop (𝓝 (-274 / 25)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (9)) (b := (46 / 5)) (m := 2) (c := (-73)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_01 hx hy)
    (by rw [W20.endpoint_46_5]; norm_num)
    (by rw [W20.integral_piece_01.2]; norm_num) hPNT
  simpa only [W20.integral_piece_01.2] using h

theorem largePrime_weighted_piece_02
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (46 / 5) (19 / 2))
      atTop (𝓝 (-3213 / 200)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (46 / 5)) (b := (19 / 2)) (m := 7) (c := (-119)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_02 hx hy)
    (by rw [W20.endpoint_19_2]; norm_num)
    (by rw [W20.integral_piece_02.2]; norm_num) hPNT
  simpa only [W20.integral_piece_02.2] using h

theorem largePrime_weighted_piece_03
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (19 / 2) (10))
      atTop (𝓝 (-195 / 8)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (19 / 2)) (b := (10)) (m := 15) (c := (-195)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_03 hx hy)
    (by rw [W20.endpoint_10]; norm_num)
    (by rw [W20.integral_piece_03.2]; norm_num) hPNT
  simpa only [W20.integral_piece_03.2] using h

theorem largePrime_weighted_piece_04
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (10) (11))
      atTop (𝓝 (-71 / 2)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (10)) (b := (11)) (m := 19) (c := (-235)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_04 hx hy)
    (by rw [W20.endpoint_11]; norm_num)
    (by rw [W20.integral_piece_04.2]; norm_num) hPNT
  simpa only [W20.integral_piece_04.2] using h

theorem largePrime_weighted_piece_05
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (11) (12))
      atTop (𝓝 (-35 / 2)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (11)) (b := (12)) (m := 17) (c := (-213)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_05 hx hy)
    (by rw [W20.endpoint_12]; norm_num)
    (by rw [W20.integral_piece_05.2]; norm_num) hPNT
  simpa only [W20.integral_piece_05.2] using h

theorem largePrime_weighted_piece_06
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (12) (15))
      atTop (𝓝 (81 / 2)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (12)) (b := (15)) (m := 15) (c := (-189)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_06 hx hy)
    (by rw [W20.endpoint_15]; norm_num)
    (by rw [W20.integral_piece_06.2]; norm_num) hPNT
  simpa only [W20.integral_piece_06.2] using h

theorem largePrime_weighted_piece_07
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (15) (16))
      atTop (𝓝 (42)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (15)) (b := (16)) (m := 12) (c := (-144)) (D := 30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_07 hx hy)
    (by rw [W20.endpoint_16]; norm_num)
    (by rw [W20.integral_piece_07.2]; norm_num) hPNT
  simpa only [W20.integral_piece_07.2] using h

theorem largePrime_weighted_piece_08
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit (16) (18))
      atTop (𝓝 (48)) := by
  have h := weighted_affine_piece_tendsto (F := W20.largePrimeLimit)
    (a := (16)) (b := (18)) (m := 6) (c := (-78)) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx hy => by simpa only [sub_eq_add_neg] using W20.piece_08 hx hy)
    (by rw [W20.endpoint_18]; norm_num)
    (by rw [W20.integral_piece_08.2]; norm_num) hPNT
  simpa only [W20.integral_piece_08.2] using h

theorem largePrime_weighted_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum W20.largePrimeLimit 9 18)
      atTop (𝓝 (261 / 10)) := by
  have h := (((((((largePrime_weighted_piece_01 hPNT).add
    (largePrime_weighted_piece_02 hPNT)).add (largePrime_weighted_piece_03 hPNT)).add
    (largePrime_weighted_piece_04 hPNT)).add (largePrime_weighted_piece_05 hPNT)).add
    (largePrime_weighted_piece_06 hPNT)).add (largePrime_weighted_piece_07 hPNT)).add
    (largePrime_weighted_piece_08 hPNT)
  have hconst :
      (-274 / 25 : ℝ) + (-3213 / 200) + (-195 / 8) + (-71 / 2) +
        (-35 / 2) + 81 / 2 + 42 + 48 = 261 / 10 := by norm_num
  rw [hconst] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (46 / 5)) (by norm_num : (46 / 5 : ℝ) ≤ (19 / 2)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (19 / 2)) (by norm_num : (19 / 2 : ℝ) ≤ (10)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (10)) (by norm_num : (10 : ℝ) ≤ (11)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (11)) (by norm_num : (11 : ℝ) ≤ (12)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (12)) (by norm_num : (12 : ℝ) ≤ (15)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (15)) (by norm_num : (15 : ℝ) ≤ (16)) hR]
  rw [weightedPrimeIntervalSum_add_adjacent W20.largePrimeLimit
    (by norm_num : (9 : ℝ) ≤ (16)) (by norm_num : (16 : ℝ) ≤ (18)) hR]

theorem largePrime_weighted_normalized_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (fun R : ℝ => (1 / 270 : ℝ) *
      weightedPrimeIntervalSum W20.largePrimeLimit 9 18 R)
      atTop (𝓝 (29 / 300)) := by
  have h := (largePrime_weighted_tendsto hPNT).const_mul (1 / 270 : ℝ)
  norm_num at h ⊢
  exact h

end Zeta5.Workers.W14

end OAI
