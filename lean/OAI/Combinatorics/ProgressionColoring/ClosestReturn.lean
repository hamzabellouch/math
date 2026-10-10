import OAI.Combinatorics.ProgressionColoring.Dichotomy
import OAI.Combinatorics.ProgressionColoring.FiniteGaps
import OAI.Combinatorics.ProgressionColoring.ClosestReturnEstimates

namespace OAI

/-!
# Closest return and its real displacement

The finite minimum-gap argument supplies a selected pair. Affinity in a small
box makes its displacement proportional to that of the two extreme selected
indices. Multiplying by the number of gaps avoids any division by the span.
-/

universe uIndex

namespace QuantitativeVanDerWaerden

/-- A short affine index gap inherits the endpoint width divided by the number
of gaps. This form makes all four evaluated representatives explicit. -/
theorem affine_pair_bound_of_packing {z : ℕ → ℝ} {a b p q : ℕ}
    {A B L n : ℝ}
    (ha : z a = A + (a : ℝ) * B) (hb : z b = A + (b : ℝ) * B)
    (hp : z p = A + (p : ℝ) * B) (hq : z q = A + (q : ℝ) * B)
    (hab : a ≤ b) (hpq : p ≤ q) (hn : 0 < n)
    (hpacking : ((b : ℝ) - a) * n ≤ (q : ℝ) - p)
    (hwidth : |z q - z p| ≤ L) : |z b - z a| ≤ L / n := by
  have hpair : z b - z a = ((b : ℝ) - a) * B := by rw [ha, hb]; ring
  have hspan : z q - z p = ((q : ℝ) - p) * B := by rw [hp, hq]; ring
  have habR : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hpqR : 0 ≤ (q : ℝ) - p := sub_nonneg.mpr (by exact_mod_cast hpq)
  apply (le_div_iff₀ hn).2
  calc
    |z b - z a| * n = (((b : ℝ) - a) * n) * |B| := by
      rw [hpair, abs_mul, abs_of_nonneg habR]
      ring
    _ ≤ ((q : ℝ) - p) * |B| := mul_le_mul_of_nonneg_right hpacking (abs_nonneg B)
    _ = |z q - z p| := by rw [hspan, abs_mul, abs_of_nonneg hpqR]
    _ ≤ L := hwidth

/-- The preceding displacement estimate on a finite selected set. -/
theorem affine_selected_pair_bound {J : Finset ℕ} (hJ : J.Nonempty)
    {z : ℕ → ℝ} {a b : ℕ} {A B L : ℝ}
    (hcard : 2 ≤ J.card) (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (haff : ∀ j ∈ J, z j = A + (j : ℝ) * B)
    (hpacking : (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ)
    (hwidth : |z (J.max' hJ) - z (J.min' hJ)| ≤ L) :
    |z b - z a| ≤ L / ((J.card : ℝ) - 1) := by
  have hp := J.min'_mem hJ
  have hq := J.max'_mem hJ
  have hpq : J.min' hJ ≤ J.max' hJ := J.min'_le _ hq
  have hc1 : 1 ≤ J.card := le_trans (by decide : 1 ≤ 2) hcard
  have hcR : (2 : ℝ) ≤ J.card := by exact_mod_cast hcard
  have hn : 0 < (J.card : ℝ) - 1 := by linarith
  have hpackingR : (((b - a) * (J.card - 1) : ℕ) : ℝ) ≤
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) := by exact_mod_cast hpacking
  rw [Nat.cast_mul, Nat.cast_sub hab.le, Nat.cast_sub hc1, Nat.cast_one,
    Nat.cast_sub hpq] at hpackingR
  exact affine_pair_bound_of_packing (haff a ha) (haff b hb)
    (haff _ hp) (haff _ hq) hab.le hpq hn hpackingR hwidth

/-- Convert the minimum-gap packing estimate into the two quotient bounds in
the closest-return argument. -/
theorem selected_gap_bounds {J : Finset ℕ} {k a b : ℕ} {M : ℝ}
    (hJ : J.Nonempty) (hJbound : ∀ j ∈ J, j < k)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card)
    (hpacking : (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ) :
    ((b - a : ℕ) : ℝ) ≤ ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ∧
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ≤ 2 * M := by
  obtain ⟨hcard, hn, hkden, _⟩ := heavy_card_estimates hM hscale hheavy
  have hc1 : 1 ≤ J.card := le_trans (by decide : 1 ≤ 2) hcard
  have hpackingR : (((b - a) * (J.card - 1) : ℕ) : ℝ) ≤
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) := by exact_mod_cast hpacking
  rw [Nat.cast_mul, Nat.cast_sub hc1, Nat.cast_one] at hpackingR
  have hspanNat : J.max' hJ - J.min' hJ ≤ k :=
    (Nat.sub_le _ _).trans (hJbound _ (J.max'_mem hJ)).le
  have hspan : ((J.max' hJ - J.min' hJ : ℕ) : ℝ) ≤ k := by exact_mod_cast hspanNat
  refine ⟨(le_div_iff₀ hn).2 hpackingR, (div_le_iff₀ hn).2 ?_⟩
  nlinarith

/-- Taking the difference of two representatives preserves the integer
congruence between the dilated and original coordinate systems. -/
theorem integer_dilation_difference {x y : ℕ → ℝ} {lam : ℝ}
    (h : ∀ j, ∃ m : ℤ, y j - lam * x j = (m : ℝ)) (a b : ℕ) :
    ∃ m : ℤ, (y b - y a) - lam * (x b - x a) = (m : ℝ) := by
  obtain ⟨ma, ha⟩ := h a
  obtain ⟨mb, hb⟩ := h b
  refine ⟨mb - ma, ?_⟩
  calc
    (y b - y a) - lam * (x b - x a) =
        (y b - lam * x b) - (y a - lam * x a) := by ring
    _ = (mb : ℝ) - (ma : ℝ) := by rw [ha, hb]
    _ = ((mb - ma : ℤ) : ℝ) := by push_cast; ring

/-- The actual closest-return and coordinate drift bounds for two systems of
real representatives of arithmetic progressions modulo one. The selected pair
and its minimality are constructed from `J`; affine behavior is proved from
the small-box hypotheses. -/
theorem exists_closest_return_drift {ι : Type uIndex} {J : Finset ℕ} {k : ℕ}
    {M H Hx lam : ℝ} {x y : ℕ → ι → ℝ} {x0 x1 y0 y1 : ι → ℝ}
    (hJbound : ∀ j ∈ J, j < k)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card)
    (hH : 0 ≤ H) (hHx : 0 ≤ Hx) (hHxH : Hx ≤ 2 * H)
    (hsmall : 2 * (k : ℝ) * H < 1)
    (hxbox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |x j d - x i d| ≤ Hx)
    (hybox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |y j d - y i d| ≤ 2 * H)
    (hxmod : ∀ j d, ∃ m : ℤ, x j d - x0 d - (j : ℝ) * x1 d = (m : ℝ))
    (hymod : ∀ j d, ∃ m : ℤ, y j d - y0 d - (j : ℝ) * y1 d = (m : ℝ))
    (hlam : 0 ≤ lam) (hlamHx : lam * Hx = H)
    (hdil : ∀ j d, ∃ m : ℤ, y j d - lam * x j d = (m : ℝ))
    (hdriftsmall : 6 * M * H / (k : ℝ) < 1) :
    ∃ j h : ℕ, j ∈ J ∧ j + h ∈ J ∧ 0 < h ∧ j + h < k ∧
      (∀ a ∈ J, ∀ b ∈ J, a < b → h ≤ b - a) ∧
      (∀ hJ : J.Nonempty,
        (h : ℝ) ≤ ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ∧
        ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ≤ 2 * M) ∧
      (h : ℝ) ≤ 2 * M ∧
      (∀ d,
        |x (j + h) d - x j d| ≤ Hx / ((J.card : ℝ) - 1) ∧
        |x (j + h) d - x j d| ≤ 2 * M * Hx / (k : ℝ) ∧
        |y (j + h) d - y j d| ≤ (2 * H) / ((J.card : ℝ) - 1) ∧
        |y (j + h) d - y j d| ≤ 4 * M * H / (k : ℝ) ∧
        y (j + h) d - y j d = lam * (x (j + h) d - x j d)) := by
  obtain ⟨hcard, hn, hkden, hk⟩ := heavy_card_estimates hM hscale hheavy
  obtain ⟨a, ha, b, hb, hab, hgap, hminimum, hpacking⟩ := exists_min_gap J hcard
  have hJ : J.Nonempty := ⟨a, ha⟩
  obtain ⟨Ax, Bx, hAx⟩ := exists_affine_of_small_box_vector J x hJbound hH hsmall
    (fun i hi j hj d => (hxbox i hi j hj d).trans hHxH)
    (fun a _ b _ c _ _ _ d =>
      triple_integral_of_integer_errors (fun j => hxmod j d) a b c)
  obtain ⟨Ay, By, hAy⟩ := exists_affine_of_small_box_vector J y hJbound hH hsmall hybox
    (fun a _ b _ c _ _ _ d =>
      triple_integral_of_integer_errors (fun j => hymod j d) a b c)
  have hbounds (hne : J.Nonempty) :=
    selected_gap_bounds hne hJbound hM hscale hheavy (hpacking hne)
  have hgapM : ((b - a : ℕ) : ℝ) ≤ 2 * M := (hbounds hJ).1.trans (hbounds hJ).2
  have heq : a + (b - a) = b := Nat.add_sub_of_le hab.le
  refine ⟨a, b - a, ?_⟩
  rw [heq]
  refine ⟨ha, hb, hgap, hJbound b hb, hminimum, hbounds, hgapM, ?_⟩
  intro d
  have hxshort : |x b d - x a d| ≤ Hx / ((J.card : ℝ) - 1) :=
    affine_selected_pair_bound hJ hcard ha hb hab (fun j hj => hAx j hj d)
      (hpacking hJ) (hxbox _ (J.min'_mem hJ) _ (J.max'_mem hJ) d)
  have hyshort : |y b d - y a d| ≤ (2 * H) / ((J.card : ℝ) - 1) :=
    affine_selected_pair_bound hJ hcard ha hb hab (fun j hj => hAy j hj d)
      (hpacking hJ) (hybox _ (J.min'_mem hJ) _ (J.max'_mem hJ) d)
  have hxrate : |x b d - x a d| ≤ 2 * M * Hx / (k : ℝ) :=
    hxshort.trans (heavy_card_rate_le hM hscale hheavy hHx)
  have hyrate : |y b d - y a d| ≤ 4 * M * H / (k : ℝ) := by
    calc
      |y b d - y a d| ≤ (2 * H) / ((J.card : ℝ) - 1) := hyshort
      _ ≤ 2 * M * (2 * H) / (k : ℝ) :=
        heavy_card_rate_le hM hscale hheavy (by positivity)
      _ = 4 * M * H / (k : ℝ) := by ring
  have hlamrate : |lam * (x b d - x a d)| ≤ 2 * M * H / (k : ℝ) := by
    rw [abs_mul, abs_of_nonneg hlam]
    calc
      lam * |x b d - x a d| ≤ lam * (2 * M * Hx / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hxrate hlam
      _ = 2 * M * (lam * Hx) / (k : ℝ) := by ring
      _ = 2 * M * H / (k : ℝ) := by rw [hlamHx]
  have hdileq : y b d - y a d = lam * (x b d - x a d) := by
    apply dilation_drift_eq (integer_dilation_difference (fun j => hdil j d) a b)
      hyrate hlamrate
    calc
      4 * M * H / (k : ℝ) + 2 * M * H / (k : ℝ) = 6 * M * H / (k : ℝ) := by ring
      _ < 1 := hdriftsmall
  exact ⟨hxshort, hxrate, hyshort, hyrate, hdileq⟩

end QuantitativeVanDerWaerden

end OAI
