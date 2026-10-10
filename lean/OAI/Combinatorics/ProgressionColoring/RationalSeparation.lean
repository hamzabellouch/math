import OAI.Combinatorics.ProgressionColoring.PrimitiveVector
import OAI.Combinatorics.ProgressionColoring.RationalReturn

namespace OAI

/-!
# Rational separation survives the real drift

The proofs use real representative differences and integral errors directly.
They do not assume a separation property of labels: it is deduced from the
primitive rational path and the proved width bound on a label's first intervals.
-/

universe uIndex uL

namespace QuantitativeVanDerWaerden

/-- The scale inequalities from the closest-return argument leave enough
space between distinct rational residues for an entire first-coordinate box. -/
theorem return_separation_margin {h : ℕ} {M H W : ℝ}
    (hh : 0 < h) (hperiod : (h : ℝ) ≤ 2 * M)
    (hW : 0 ≤ W) (hWH : W ≤ H) (hsmall : 4 * M * H < 1) :
    W + (2 * M * W) / h < 1 / (h : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hM : 0 ≤ M := by linarith
  have h₁ := mul_le_mul_of_nonneg_right hperiod hW
  have h₂ := mul_le_mul_of_nonneg_left hWH (show 0 ≤ 4 * M by positivity)
  apply (lt_div_iff₀ hhR).2
  have hcancel : (2 * M * W / (h : ℝ)) * h = 2 * M * W :=
    div_mul_cancel₀ _ hhR.ne'
  nlinarith

/-- The drift accumulated between two indices in the progression is at most
the full-length drift divided by the return denominator. -/
theorem index_drift_le {a b k h : ℕ} {u U : ℝ}
    (ha : a < k) (hb : b < k) (hh : 0 < h)
    (hu : (k : ℝ) * |u| ≤ U) :
    |((a : ℝ) - b) / h * u| ≤ U / h := by
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hak : (a : ℝ) ≤ k := by exact_mod_cast ha.le
  have hbk : (b : ℝ) ≤ k := by exact_mod_cast hb.le
  have hd : |(a : ℝ) - b| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  calc
    _ = (|(a : ℝ) - b| * |u|) / h := by
      rw [abs_mul, abs_div, abs_of_pos hhR]
      ring
    _ ≤ ((k : ℝ) * |u|) / h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (abs_nonneg u)) hhR.le
    _ ≤ U / h := div_le_div_of_nonneg_right hu hhR.le

/-- Indices incongruent modulo the primitive denominator have a separated
coordinate, even after adding the actual small drift and choosing representatives. -/
theorem rational_path_coordinate_separation {ι : Type uIndex} [Fintype ι]
    {k h a b : ℕ} {W U : ℝ} {t : ι → ℤ}
    (X : ℕ → ι → ℝ) (A u : ι → ℝ)
    (hh : 0 < h) (hp : PrimitiveVector h t)
    (hpath : ∀ n, n < k → ∀ i, ∃ z : ℤ,
      X n i - A i - (n : ℝ) / h * ((t i : ℝ) + u i) = z)
    (hdrift : ∀ i, (k : ℝ) * |u i| ≤ U)
    (hmargin : W + U / h < 1 / (h : ℝ))
    (ha : a < k) (hb : b < k) (hab : ¬ (h : ℤ) ∣ (a : ℤ) - b) :
    ∃ i, W < |X a i - X b i| := by
  obtain ⟨i, hi⟩ := hp.exists_separated_coordinate hh hab
  refine ⟨i, ?_⟩
  obtain ⟨za, hza⟩ := hpath a ha i
  obtain ⟨zb, hzb⟩ := hpath b hb i
  have hid : (((a : ℤ) - b : ℤ) : ℝ) * (t i : ℝ) / h -
      ((-(za - zb) : ℤ) : ℝ) =
      (X a i - X b i) - ((a : ℝ) - b) / h * u i := by
    push_cast
    calc
      _ = ((a : ℝ) / h * ((t i : ℝ) + u i) -
          (b : ℝ) / h * ((t i : ℝ) + u i)) +
          ((za : ℝ) - zb) - ((a : ℝ) - b) / h * u i := by ring
      _ = _ := by linarith
  have hsep := hi (-(za - zb))
  rw [hid] at hsep
  have htriangle := abs_sub (X a i - X b i) (((a : ℝ) - b) / h * u i)
  have hsmall := index_drift_le ha hb hh (hdrift i)
  by_contra hnot
  have hle : |X a i - X b i| ≤ W := le_of_not_gt hnot
  linarith

/-- Every occurrence of one label lies in one residue class. The label
hypothesis is only its actual coordinate-width bound. -/
theorem same_label_divisible_index_difference {ι : Type uIndex} {L : Type uL} [Fintype ι]
    {k h a b : ℕ} {W U : ℝ} {t : ι → ℤ}
    (X : ℕ → ι → ℝ) (A u : ι → ℝ) (label : ℕ → L)
    (hh : 0 < h) (hp : PrimitiveVector h t)
    (hpath : ∀ n, n < k → ∀ i, ∃ z : ℤ,
      X n i - A i - (n : ℝ) / h * ((t i : ℝ) + u i) = z)
    (hdrift : ∀ i, (k : ℝ) * |u i| ≤ U)
    (hmargin : W + U / h < 1 / (h : ℝ))
    (hwidth : ∀ n, n < k → ∀ m, m < k → label n = label m →
      ∀ i, |X n i - X m i| ≤ W)
    (ha : a < k) (hb : b < k) (hlab : label a = label b) :
    (h : ℤ) ∣ (a : ℤ) - b := by
  by_contra hn
  obtain ⟨i, hi⟩ := rational_path_coordinate_separation X A u hh hp hpath
    hdrift hmargin ha hb hn
  exact (not_lt_of_ge (hwidth a ha b hb hlab i)) hi

end QuantitativeVanDerWaerden

end OAI
