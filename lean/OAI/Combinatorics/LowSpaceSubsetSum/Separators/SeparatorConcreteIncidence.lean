import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplingBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorIncidence

namespace OAI

/-! # Both incidence bounds for the actual rounded separating families -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

private theorem choose_diagonal_le (a b d : ℕ) : a.choose b ≤ (a + d).choose (b + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.choose_succ_succ]
    exact ih.trans (Nat.le_add_right _ _)

theorem separator_denominator_le (g e c : ℕ) (hc : c ≤ g / 2) (hce : c ≤ e) :
    (g / 2).choose (e - c) ≤ g.choose e := by
  have h := choose_diagonal_le (g / 2) (e - c) c
  rw [Nat.sub_add_cancel hce] at h
  exact h.trans (Nat.choose_le_choose e (by omega))

theorem rounded_containment_incidence (g c e : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hce : c ≤ e) (heg : e ≤ g) (hfeas : e - c ≤ g / 2)
    {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3))
    (hc : |(c : ℝ) - (g : ℝ) * k| ≤ 1)
    (he : |(e : ℝ) - (g : ℝ) * (k + separatorY k)| ≤ 2) :
    (⌈10 / ((Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e)⌉₊ : ℝ) *
      ((Nat.choose (g - c) (e - c) : ℝ) / Nat.choose g e) ≤
        (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) *
          (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  have hcHalf : c ≤ g / 2 := by
    have hcu := (abs_le.mp hc).2
    have hgc := mul_le_mul_of_nonneg_left hk.2 (Nat.cast_nonneg g)
    have hgR : (64 : ℝ) ≤ g := by exact_mod_cast hg
    have hhalf : ((g / 2 : ℕ) : ℝ) = (g : ℝ) / 2 := Nat.cast_div heven (by norm_num)
    have h : (c : ℝ) ≤ (g / 2 : ℕ) := by rw [hhalf]; nlinarith
    exact_mod_cast h
  exact (rounded_family_incidence ((g - c).choose (e - c)) ((g / 2).choose (e - c))
    (g.choose e) (Nat.choose_pos hfeas) (Nat.choose_pos heg)
    (separator_denominator_le g e c hcHalf hce)).trans
    (rounded_separator_incidence_bound g c e hg heven hce heg hfeas hk hc he)

/-- Complementing both prescribed counts preserves their rounding errors.
This supplies the right-array bound from the same sharp entropy estimate. -/
theorem complement_rounding (g c e : ℕ) (heven : 2 ∣ g) (hcHalf : c ≤ g / 2)
    (heg : e ≤ g) (k : ℝ) :
    ((g / 2 - c : ℕ) : ℝ) - (g : ℝ) * (1 / 2 - k) =
        -((c : ℝ) - (g : ℝ) * k) ∧
    ((g - e : ℕ) : ℝ) - (g : ℝ) * ((1 / 2 - k) + separatorY (1 / 2 - k)) =
        -((e : ℝ) - (g : ℝ) * (k + separatorY k)) := by
  have hhalf : ((g / 2 : ℕ) : ℝ) = (g : ℝ) / 2 := Nat.cast_div heven (by norm_num)
  rw [Nat.cast_sub hcHalf, Nat.cast_sub heg, hhalf]
  unfold separatorY
  constructor <;> ring

theorem rounded_avoidance_incidence (g c e : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hcHalf : c ≤ g / 2) (hce : c ≤ e) (heg : e ≤ g) (hfeas : e - c ≤ g / 2)
    {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3))
    (hc : |(c : ℝ) - (g : ℝ) * k| ≤ 1)
    (he : |(e : ℝ) - (g : ℝ) * (k + separatorY k)| ≤ 2) :
    (⌈10 / ((Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e)⌉₊ : ℝ) *
      ((Nat.choose (g - (g / 2 - c)) e : ℝ) / Nat.choose g e) ≤
        (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) *
          (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  have hg2 : 2 * (g / 2) = g := Nat.mul_div_cancel' heven
  have hce' : g / 2 - c ≤ g - e := by omega
  have hf' : g - e - (g / 2 - c) ≤ g / 2 := by omega
  have hk' : 1 / 2 - k ∈ Set.Icc (1 / 6 : ℝ) (1 / 3) := by
    constructor <;> linarith [hk.1, hk.2]
  obtain ⟨hcr, her⟩ := complement_rounding g c e heven hcHalf heg k
  have h := rounded_containment_incidence g (g / 2 - c) (g - e) hg heven
    hce' (Nat.sub_le _ _) hf' hk'
    (by rw [hcr, abs_neg]; exact hc) (by rw [her, abs_neg]; exact he)
  have hN : g.choose (g - e) = g.choose e := Nat.choose_symm heg
  have hD : (g / 2).choose (g - e - (g / 2 - c)) = (g / 2).choose (e - c) := by
    have hi : g - e - (g / 2 - c) = g / 2 - (e - c) := by omega
    rw [hi, Nat.choose_symm hfeas]
  have hA : (g - (g / 2 - c)).choose (g - e - (g / 2 - c)) =
      (g - (g / 2 - c)).choose e := by
    have hi : g - e - (g / 2 - c) = g - (g / 2 - c) - e := by omega
    rw [hi, Nat.choose_symm (by omega : e ≤ g - (g / 2 - c))]
  rwa [hN, hD, hA] at h

end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
