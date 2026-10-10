import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEntropy
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-!
# Rounded separator incidence estimates

The sharp entropy estimate remains useful after the integer cardinalities
are rounded. We use a fixed compact interval and explicit constant error,
so that rounding introduces a constant factor rather than exponential slack.
-/

namespace LowSpaceSubsetSum

private theorem logb_two_eight : Real.logb 2 8 = 3 := by
  have h := Real.logb_pow 2 2 3
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  exact h

private theorem hasDerivAt_binaryEntropy_compact {p : ℝ}
    (hp : p ∈ Set.Icc (1 / 8) (7 / 8)) :
    HasDerivAt binaryEntropy (Real.logb 2 ((1 - p) / p)) p := by
  have hp0 : p ≠ 0 := by linarith [hp.1]
  have hp1 : p ≠ 1 := by linarith [hp.2]
  have hs : 1 - p ≠ 0 := by linarith [hp.2]
  convert! (Real.hasDerivAt_binEntropy hp0 hp1).div_const (Real.log 2) using 1
  unfold Real.logb
  rw [Real.log_div hs hp0]

private theorem binaryEntropy_deriv_bound {p : ℝ}
    (hp : p ∈ Set.Icc (1 / 8) (7 / 8)) :
    |Real.logb 2 ((1 - p) / p)| ≤ 3 := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hs : 0 < 1 - p := by linarith [hp.2]
  have hl : (1 / 8 : ℝ) ≤ (1 - p) / p :=
    (le_div_iff₀ hp0).mpr (by linarith [hp.2])
  have hu : (1 - p) / p ≤ 8 := (div_le_iff₀ hp0).mpr (by linarith [hp.1])
  have hlo := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1 / 8) hl
  have hhi := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos hs hp0) hu
  rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_one, logb_two_eight] at hlo
  rw [logb_two_eight] at hhi
  exact abs_le.mpr ⟨by linarith, hhi⟩

/-- A fixed constant suffices for every density used by the rounded separator. -/
theorem binaryEntropy_lipschitz_compact {p q : ℝ}
    (hp : p ∈ Set.Icc (1 / 8) (7 / 8)) (hq : q ∈ Set.Icc (1 / 8) (7 / 8)) :
    |binaryEntropy p - binaryEntropy q| ≤ 3 * |p - q| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hasDerivAt_binaryEntropy_compact hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using binaryEntropy_deriv_bound hx)
    (convex_Icc (1 / 8 : ℝ) (7 / 8)) hq hp
  simpa only [Real.norm_eq_abs] using h

/-- The floor-computed rational slope used in the sampling rule. -/
noncomputable def separatorRationalAlpha (m : ℕ) : ℝ :=
  (⌊(m : ℝ) * separatorAlpha⌋ : ℤ) / (m : ℝ)

theorem separatorRationalAlpha_error {m : ℕ} (hm : 0 < m) :
    0 ≤ separatorAlpha - separatorRationalAlpha m ∧
      separatorAlpha - separatorRationalAlpha m < 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hf := Int.floor_le ((m : ℝ) * separatorAlpha)
  have hfl := Int.lt_floor_add_one ((m : ℝ) * separatorAlpha)
  have heq : (separatorAlpha - separatorRationalAlpha m) * m =
      (m : ℝ) * separatorAlpha - (⌊(m : ℝ) * separatorAlpha⌋ : ℤ) := by
    unfold separatorRationalAlpha
    field_simp
  constructor
  · apply nonneg_of_mul_nonneg_left (b := (m : ℝ)) ?_ hm0
    rw [heq]
    linarith
  · apply (lt_div_iff₀ hm0).mpr
    rw [heq]
    linarith

theorem separatorRationalAlpha_eq_log_power (m : ℕ) :
    separatorRationalAlpha m = (⌊Real.logb 2 ((3 : ℝ) ^ m)⌋ : ℤ) / (m : ℝ) := by
  rw [Real.logb_pow]
  rfl

/-- Approximating the slope by its integer-log version costs at most one
in the prescribed sample size whenever the block fits inside the mixer. -/
theorem separatorRationalAlpha_sample_error {g m : ℕ} (hm : 0 < m) (hgm : g ≤ m)
    {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    |(g : ℝ) * (1 / 2 + separatorRationalAlpha m * (k - 1 / 4)) -
      (g : ℝ) * (k + separatorY k)| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := separatorRationalAlpha_error hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgm' : (g : ℝ) ≤ m := by exact_mod_cast hgm
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hscale : (g : ℝ) * (separatorAlpha - separatorRationalAlpha m) ≤ 1 := by
    calc
      _ ≤ (g : ℝ) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hhi.le hg0
      _ ≤ 1 := by rw [mul_one_div]; exact (div_le_one hm0).mpr hgm'
  have hnonneg : 0 ≤ (g : ℝ) * (separatorAlpha - separatorRationalAlpha m) :=
    mul_nonneg hg0 hlo
  have hk' : |k - 1 / 4| ≤ 1 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hid : (g : ℝ) * (1 / 2 + separatorRationalAlpha m * (k - 1 / 4)) -
      (g : ℝ) * (k + separatorY k) =
      -((g : ℝ) * (separatorAlpha - separatorRationalAlpha m) * (k - 1 / 4)) := by
    unfold separatorY
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hnonneg]
  exact (mul_le_mul_of_nonneg_left hk' hnonneg).trans (by simpa only [mul_one] using hscale)

/-- The actual outer floor plus the rational-slope approximation satisfies
the two-unit error used in the incidence theorem. -/
theorem separator_sample_floor_error {g m e : ℕ} (hm : 0 < m) (hgm : g ≤ m)
    {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3))
    (he : (e : ℤ) = ⌊(g : ℝ) * (1 / 2 + separatorRationalAlpha m * (k - 1 / 4))⌋) :
    |(e : ℝ) - (g : ℝ) * (k + separatorY k)| ≤ 2 := by
  let x := (g : ℝ) * (1 / 2 + separatorRationalAlpha m * (k - 1 / 4))
  have hfloor : |(e : ℝ) - x| ≤ 1 := by
    have hcast : (e : ℝ) = (⌊x⌋ : ℤ) := by exact_mod_cast he
    rw [hcast, abs_of_nonpos (by linarith [Int.floor_le x])]
    linarith [Int.lt_floor_add_one x]
  have hslope := separatorRationalAlpha_sample_error hm hgm hk
  calc
    _ = |((e : ℝ) - x) + (x - (g : ℝ) * (k + separatorY k))| := by congr 1; ring
    _ ≤ |(e : ℝ) - x| + |x - (g : ℝ) * (k + separatorY k)| := abs_add_le _ _
    _ ≤ 2 := by linarith

theorem separator_density_bounds {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    separatorX k ∈ Set.Icc (2 / 3) (5 / 6) ∧
      separatorY k ∈ Set.Icc (1 / 6) (1 / 3) := by
  obtain ⟨ha1, ha2⟩ := separatorAlpha_bounds
  have hl := mul_le_mul_of_nonneg_left hk.1 (show 0 ≤ separatorAlpha - 1 by linarith)
  have hu := mul_le_mul_of_nonneg_left hk.2 (show 0 ≤ separatorAlpha - 1 by linarith)
  constructor
  · unfold separatorX
    constructor <;> linarith [hk.1, hk.2]
  · unfold separatorY
    constructor <;> nlinarith

/-- A weighted form avoids dividing a rounding error by a small block size. -/
theorem weighted_binaryEntropy_error {a b p q : ℝ} (ha : 0 ≤ a)
    (hp : p ∈ Set.Icc (1 / 8) (7 / 8)) (hq : q ∈ Set.Icc (1 / 8) (7 / 8)) :
    |a * binaryEntropy p - b * binaryEntropy q| ≤
      3 * |a * p - b * q| + 4 * |a - b| := by
  have hqabs : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hhq : |binaryEntropy q| ≤ 1 := by
    rw [abs_of_nonneg (binaryEntropy_nonneg (by linarith [hq.1]) (by linarith [hq.2]))]
    exact binaryEntropy_le_one q
  have hprod : |(a - b) * q| ≤ |a - b| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hqabs (abs_nonneg (a - b))
  have hdist : a * |p - q| ≤ |a * p - b * q| + |a - b| := by
    calc
      _ = |a * (p - q)| := by rw [abs_mul, abs_of_nonneg ha]
      _ = |(a * p - b * q) - (a - b) * q| := by congr 1; ring
      _ ≤ |a * p - b * q| + |(a - b) * q| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl hprod
  have hprod' : |(a - b) * binaryEntropy q| ≤ |a - b| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hhq (abs_nonneg (a - b))
  have hmain : |a * binaryEntropy p - b * binaryEntropy q| ≤
      a * |binaryEntropy p - binaryEntropy q| + |a - b| := by
    calc
      _ = |a * (binaryEntropy p - binaryEntropy q) + (a - b) * binaryEntropy q| :=
        by congr 1; ring
      _ ≤ |a * (binaryEntropy p - binaryEntropy q)| + |(a - b) * binaryEntropy q| :=
        abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg ha]; exact add_le_add le_rfl hprod'
  have hLip := mul_le_mul_of_nonneg_left (binaryEntropy_lipschitz_compact hp hq) ha
  nlinarith

/-- The binomial entropy bounds turn an exponent gap into a ratio bound. -/
theorem choose_ratio_le_of_entropy_gap (n d j : ℕ) (hjn : j ≤ n) (hjd : j ≤ d)
    {T : ℝ} (hT : (n : ℝ) * binaryEntropy ((j : ℝ) / n) -
      (d : ℝ) * binaryEntropy ((j : ℝ) / d) ≤ T) :
    (n.choose j : ℝ) / (d.choose j : ℝ) ≤
      ((d : ℝ) + 1) * (2 : ℝ) ^ T := by
  have hnpos : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn
  have hdpos : (0 : ℝ) < d.choose j := by exact_mod_cast Nat.choose_pos hjd
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hlogN := (logb_choose_bounds n j hjn).2
  have hlogD := (logb_choose_bounds d j hjd).1
  have hlog : Real.logb 2 ((n.choose j : ℝ) / (d.choose j : ℝ)) ≤
      T + Real.logb 2 ((d : ℝ) + 1) := by
    rw [Real.logb_div (ne_of_gt hnpos) (ne_of_gt hdpos)]
    linarith
  calc
    _ = (2 : ℝ) ^ Real.logb 2 ((n.choose j : ℝ) / (d.choose j : ℝ)) :=
      (Real.rpow_logb (by norm_num) (by norm_num) (div_pos hnpos hdpos)).symm
    _ ≤ (2 : ℝ) ^ (T + Real.logb 2 ((d : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
    _ = ((d : ℝ) + 1) * (2 : ℝ) ^ T := by
      rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hd1]
      ring

/-- Bounded rounding changes the difference of the two entropy exponents
by at most `22`, uniformly over the entire allowed density interval. -/
theorem rounded_separator_entropy_gap (g c e : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hce : c ≤ e) (heg : e ≤ g) {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3))
    (hc : |(c : ℝ) - (g : ℝ) * k| ≤ 1)
    (he : |(e : ℝ) - (g : ℝ) * (k + separatorY k)| ≤ 2) :
    ((g - c : ℕ) : ℝ) * binaryEntropy (((e - c : ℕ) : ℝ) / (g - c : ℕ)) -
      ((g / 2 : ℕ) : ℝ) * binaryEntropy (((e - c : ℕ) : ℝ) / (g / 2 : ℕ)) ≤
      (g : ℝ) * (1 - binaryEntropy (1 / 4)) + 22 := by
  let G : ℝ := g
  let N : ℝ := (g - c : ℕ)
  let J : ℝ := (e - c : ℕ)
  let D : ℝ := (g / 2 : ℕ)
  have hG : 64 ≤ G := by
    change (64 : ℝ) ≤ (g : ℝ)
    exact_mod_cast hg
  have hG0 : 0 ≤ G := by linarith
  have hN : N = G - c := by dsimp [N, G]; exact Nat.cast_sub (hce.trans heg)
  have hJ : J = (e : ℝ) - c := by dsimp [J]; exact Nat.cast_sub hce
  have hD : D = G / 2 := by dsimp [D, G]; exact Nat.cast_div heven (by norm_num)
  obtain ⟨hX, hY⟩ := separator_density_bounds hk
  have hX0 : 0 < separatorX k := by linarith [hX.1]
  have hNr : |N - G * separatorX k| ≤ 1 := by
    have hid : N - G * separatorX k = -((c : ℝ) - G * k) := by
      rw [hN]
      unfold separatorX
      ring
    rw [hid, abs_neg]
    exact hc
  have hJr : |J - G * separatorY k| ≤ 3 := by
    have hid : J - G * separatorY k =
        ((e : ℝ) - G * (k + separatorY k)) - ((c : ℝ) - G * k) := by
      rw [hJ]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hNb := abs_le.mp hNr
  have hJb := abs_le.mp hJr
  have hNlo : (2 / 3) * G - 1 ≤ N := by
    have h := mul_le_mul_of_nonneg_left hX.1 hG0
    nlinarith
  have hNhi : N ≤ (5 / 6) * G + 1 := by
    have h := mul_le_mul_of_nonneg_left hX.2 hG0
    nlinarith
  have hJlo : (1 / 6) * G - 3 ≤ J := by
    have h := mul_le_mul_of_nonneg_left hY.1 hG0
    nlinarith
  have hJhi : J ≤ (1 / 3) * G + 3 := by
    have h := mul_le_mul_of_nonneg_left hY.2 hG0
    nlinarith
  have hN0 : 0 < N := by linarith
  have hD0 : 0 < D := by rw [hD]; linarith
  have hp : J / N ∈ Set.Icc (1 / 8) (7 / 8) := by
    constructor
    · exact (le_div_iff₀ hN0).mpr (by linarith)
    · exact (div_le_iff₀ hN0).mpr (by linarith)
  have hp' : J / D ∈ Set.Icc (1 / 8) (7 / 8) := by
    rw [hD]
    constructor
    · exact (le_div_iff₀ (by linarith : 0 < G / 2)).mpr (by linarith)
    · exact (div_le_iff₀ (by linarith : 0 < G / 2)).mpr (by linarith)
  have hq : separatorY k / separatorX k ∈ Set.Icc (1 / 8) (7 / 8) := by
    constructor
    · exact (le_div_iff₀ hX0).mpr (by linarith [hX.2, hY.1])
    · exact (div_le_iff₀ hX0).mpr (by linarith [hX.1, hY.2])
  have hq' : 2 * separatorY k ∈ Set.Icc (1 / 8) (7 / 8) := by
    constructor <;> linarith [hY.1, hY.2]
  have hprodN : N * (J / N) = J := by field_simp
  have hprodG : G * separatorX k * (separatorY k / separatorX k) =
      G * separatorY k := by field_simp
  have hprodD : D * (J / D) = J := by field_simp
  have hprodDY : D * (2 * separatorY k) = G * separatorY k := by rw [hD]; ring
  have hEN : |N * binaryEntropy (J / N) -
      (G * separatorX k) * binaryEntropy (separatorY k / separatorX k)| ≤ 13 := by
    have h := weighted_binaryEntropy_error hN0.le hp hq (b := G * separatorX k)
    rw [hprodN, hprodG] at h
    linarith
  have hED : |D * binaryEntropy (J / D) - D * binaryEntropy (2 * separatorY k)| ≤ 9 := by
    have h := weighted_binaryEntropy_error hD0.le hp' hq' (b := D)
    rw [hprodD, hprodDY, sub_self, abs_zero, mul_zero, add_zero] at h
    linarith
  have hsharp := mul_le_mul_of_nonneg_left (separatorEntropy_le hk) hG0
  unfold separatorEntropy at hsharp
  change N * binaryEntropy (J / N) - D * binaryEntropy (J / D) ≤ _
  rw [hD] at hED ⊢
  have hnhi := (abs_le.mp hEN).2
  have hdlo := (abs_le.mp hED).1
  nlinarith

/-- The rounded separator incidence bound has only a linear polynomial
factor. The constant is `11 * 2^22 = 46,137,344`. -/
theorem rounded_separator_incidence_bound (g c e : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hce : c ≤ e) (heg : e ≤ g) (hjd : e - c ≤ g / 2)
    {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3))
    (hc : |(c : ℝ) - (g : ℝ) * k| ≤ 1)
    (he : |(e : ℝ) - (g : ℝ) * (k + separatorY k)| ≤ 2) :
    11 * ((Nat.choose (g - c) (e - c) : ℝ) / Nat.choose (g / 2) (e - c)) ≤
      (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) *
        (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  have hgap := rounded_separator_entropy_gap g c e hg heven hce heg hk hc he
  have hratio := choose_ratio_le_of_entropy_gap (g - c) (g / 2) (e - c)
    (by omega) hjd hgap
  have hdle : ((g / 2 : ℕ) : ℝ) + 1 ≤ (g : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.div_le_self g 2) 1
  have hpow : (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4)) + 22) =
      2 ^ 22 * (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) := by
    rw [Real.rpow_add (by norm_num)]
    norm_num [mul_comm]
  rw [hpow] at hratio
  have hnonneg : 0 ≤ (2 ^ 22 : ℝ) * (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) :=
    by positivity
  have h := hratio.trans (mul_le_mul_of_nonneg_right hdle hnonneg)
  nlinarith

end LowSpaceSubsetSum

end OAI
