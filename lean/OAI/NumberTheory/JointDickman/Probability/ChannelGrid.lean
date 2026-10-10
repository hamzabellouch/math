import OAI.NumberTheory.JointDickman.Probability.ResidueChannelDecay

namespace OAI

/-! # The manuscript's refining logarithmic grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def channelFineCount (m₁ B : ℕ) : ℕ :=
  m₁ * ⌈((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m₁⌉₊

noncomputable def channelMesh (n : ℕ) : ℝ := (5 / 2 : ℝ) / n

noncomputable def channelLower (n : ℕ) (i : Fin n) : ℝ :=
  1 / 2 + (i.val : ℝ) * channelMesh n

noncomputable def channelUpper (n : ℕ) (i : Fin n) : ℝ :=
  1 / 2 + ((i.val : ℝ) + 1) * channelMesh n

theorem channelFineCount_pos {m₁ B : ℕ} (hm : 0 < m₁) (hB : 0 < B) :
    0 < channelFineCount m₁ B := by
  apply Nat.mul_pos hm
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hB) _))
    (by exact_mod_cast hm)

theorem channelFineCount_upper {m₁ : ℕ} (hm : 0 < m₁) (B : ℕ) :
    (channelFineCount m₁ B : ℝ) ≤ (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) + m₁ := by
  have hm0 : (0 : ℝ) < m₁ := by exact_mod_cast hm
  have h := (Nat.ceil_lt_add_one (show 0 ≤ ((5 / 2 : ℝ) *
      (B : ℝ) ^ (11 / 10 : ℝ)) / m₁ by positivity)).le
  have h' := mul_le_mul_of_nonneg_left h hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_add, mul_one,
    mul_div_cancel₀ _ hm0.ne'] using h'

theorem channelFineCount_eventually_le_square {m₁ : ℕ} (hm : 0 < m₁) :
    ∀ᶠ B : ℕ in atTop, (channelFineCount m₁ B : ℝ) ≤ (B : ℝ) ^ 2 := by
  have hsmall : Tendsto (fun B : ℕ =>
      ((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) + m₁) / (B : ℝ) ^ 2) atTop (𝓝 0) := by
    have h₁ := ((power_div_power_tendsto_zero (by norm_num : (11 / 10 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop).const_mul (5 / 2 : ℝ)
    have h₂ : Tendsto (fun B : ℕ => (m₁ : ℝ) / (B : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, Real.rpow_two, add_div, mul_div_assoc, add_zero, mul_zero] using h₁.add h₂
  filter_upwards [hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  exact (channelFineCount_upper hm B).trans
    ((div_lt_one (by positivity : (0 : ℝ) < (B : ℝ) ^ 2)).mp hsmallB).le

theorem channelMesh_pos {n : ℕ} (hn : 0 < n) : 0 < channelMesh n :=
  div_pos (by norm_num) (by exact_mod_cast hn)

theorem channel_width (n : ℕ) (i : Fin n) : channelUpper n i - channelLower n i = channelMesh n := by
  unfold channelUpper channelLower
  ring

theorem channelLower_ge (n : ℕ) (i : Fin n) : 1 / 2 ≤ channelLower n i := by
  unfold channelLower channelMesh
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by positivity))

theorem channelUpper_le {n : ℕ} (hn : 0 < n) (i : Fin n) : channelUpper n i ≤ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have h := mul_le_mul_of_nonneg_right hi (channelMesh_pos hn).le
  have heq : (n : ℝ) * channelMesh n = 5 / 2 := by
    unfold channelMesh
    field_simp
  unfold channelUpper
  linarith

theorem channelCells_disjoint {n : ℕ} (hn : 0 < n) (i j : Fin n) (s : ℝ)
    (hi : s ∈ Set.Ioc (channelLower n i) (channelUpper n i))
    (hj : s ∈ Set.Ioc (channelLower n j) (channelUpper n j)) : i = j := by
  apply Fin.ext
  have hmesh := channelMesh_pos hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hij : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
    have hle : channelUpper n i ≤ channelLower n j := by
      unfold channelUpper channelLower
      nlinarith
    exact (not_lt_of_ge (hi.2.trans hle)) hj.1
  · have hji : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hgt
    have hle : channelUpper n j ≤ channelLower n i := by
      unfold channelUpper channelLower
      nlinarith
    exact (not_lt_of_ge (hj.2.trans hle)) hi.1

theorem channel_total_mass {n q : ℕ} [NeZero q] (hn : 0 < n) :
    (∑ _a : Fin n × (ZMod q)ˣ, channelMesh n / (q.totient : ℝ)) = 5 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hq0 : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin,
    ZMod.card_units_eq_totient, Nat.cast_mul, channelMesh]
  field_simp

theorem channel_atom_lower {n q B : ℕ} [NeZero q] (hB : 0 < B)
    (hn : 0 < n) (hnB : (n : ℝ) ≤ (B : ℝ) ^ 2) (hqB : q ≤ B) :
    (B : ℝ) ^ (-(3 : ℝ)) ≤ channelMesh n / (q.totient : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hφ : (q.totient : ℝ) ≤ B := by exact_mod_cast (Nat.totient_le q).trans hqB
  have hprod : (n : ℝ) * q.totient ≤ (B : ℝ) ^ 3 := by
    calc
      _ ≤ (B : ℝ) ^ 2 * B := mul_le_mul hnB hφ hq0.le (by positivity)
      _ = _ := by ring
  rw [Real.rpow_neg hB0.le]
  rw [Real.rpow_ofNat]
  unfold channelMesh
  rw [div_div, ← one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ 3)
    (mul_pos hn0 hq0)).mpr
  nlinarith [pow_pos hB0 3]

end JointDickman

end OAI
