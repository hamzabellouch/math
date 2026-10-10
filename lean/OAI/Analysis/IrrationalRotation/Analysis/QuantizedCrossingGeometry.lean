import OAI.Analysis.IrrationalRotation.Analysis.UniformQuantization

namespace OAI

noncomputable section
open Set

namespace Invariant233.UniformQuantization

theorem radix_bin_subset_top {q : ℕ} [NeZero q] (a : Fin q)
    {t u w : ℝ}
    (ht : t ∈ Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q))
    (htu : t < u) (hu : u ≤ 1 - w) (hmargin : 1 / (q : ℝ) < w / 2) :
    Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) ⊆ Ico 0 (1 - w / 2) := by
  intro x hx
  have hlow : 0 ≤ (a : ℝ) / q := by positivity
  have hsplit : ((a : ℝ) + 1) / q = (a : ℝ) / q + 1 / q := by ring
  refine ⟨hlow.trans hx.1, ?_⟩
  rw [hsplit] at hx
  linarith [ht.1, hx.2]

theorem radix_bin_subset_bottom {q : ℕ} [NeZero q] (a : Fin q)
    {t u w : ℝ}
    (ht : t ∈ Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q))
    (hut : u ≤ t) (hu : w ≤ u) (hmargin : 1 / (q : ℝ) < w / 2) :
    Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) ⊆ Ico (w / 2) 1 := by
  intro x hx
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ha : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt a.isLt
  have hupper : ((a : ℝ) + 1) / q ≤ 1 := (div_le_iff₀ hq).mpr (by linarith)
  have hsplit : ((a : ℝ) + 1) / q = (a : ℝ) / q + 1 / q := by ring
  refine ⟨?_, hx.2.trans_le hupper⟩
  rw [hsplit] at ht
  linarith [ht.2, hx.1]

theorem quantize_bin_subset_top {q : ℕ} [NeZero q] {t u w : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (htu : t < u) (hu : u ≤ 1 - w)
    (hmargin : 1 / (q : ℝ) < w / 2) :
    Ico ((quantize q t : ℝ) / q) (((quantize q t : ℝ) + 1) / q) ⊆
      Ico 0 (1 - w / 2) :=
  radix_bin_subset_top (quantize q t) ((quantize_eq_iff _ ht).mp rfl) htu hu hmargin

theorem quantize_bin_subset_bottom {q : ℕ} [NeZero q] {t u w : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hut : u ≤ t) (hu : w ≤ u)
    (hmargin : 1 / (q : ℝ) < w / 2) :
    Ico ((quantize q t : ℝ) / q) (((quantize q t : ℝ) + 1) / q) ⊆
      Ico (w / 2) 1 :=
  radix_bin_subset_bottom (quantize q t) ((quantize_eq_iff _ ht).mp rfl) hut hu hmargin

theorem raw_mem_top_of_same_digit {q : ℕ} [NeZero q] {X t u w : ℝ}
    (hX : X ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (hdigit : quantize q X = quantize q t)
    (htu : t < u) (hu : u ≤ 1 - w) (hmargin : 1 / (q : ℝ) < w / 2) :
    X ∈ Ico 0 (1 - w / 2) :=
  quantize_bin_subset_top ht htu hu hmargin ((quantize_eq_iff _ hX).mp hdigit)

theorem raw_mem_bottom_of_same_digit {q : ℕ} [NeZero q] {Y t u w : ℝ}
    (hY : Y ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (hdigit : quantize q Y = quantize q t)
    (hut : u ≤ t) (hu : w ≤ u) (hmargin : 1 / (q : ℝ) < w / 2) :
    Y ∈ Ico (w / 2) 1 :=
  quantize_bin_subset_bottom ht hut hu hmargin ((quantize_eq_iff _ hY).mp hdigit)

theorem rounded_top_forces_crossing {q : ℕ} {Y t u w : ℝ}
    (hY : 1 - w / 2 ≤ Y) (hround : |t - Y| ≤ 1 / (q : ℝ))
    (hu : u ≤ 1 - w) (hmargin : 1 / (q : ℝ) < w / 2) : u < t := by
  have h := (abs_le.mp hround).1
  linarith

theorem rounded_bottom_forces_crossing {q : ℕ} {X t u w : ℝ}
    (hX : X ≤ w / 2) (hround : |t - X| ≤ 1 / (q : ℝ))
    (hu : w ≤ u) (hmargin : 1 / (q : ℝ) < w / 2) : t < u := by
  have h := (abs_le.mp hround).2
  linarith

end Invariant233.UniformQuantization

end

end OAI
