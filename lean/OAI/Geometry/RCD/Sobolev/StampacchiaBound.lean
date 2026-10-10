import OAI.Geometry.RCD.Sobolev.StampacchiaDecay

namespace OAI

/-! # A uniform extinction level for the torsion superlevel recurrence -/

open Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

/-- The extinction level depends only on the coefficient, exponent, and
initial volume bound, not on the particular decreasing distribution. -/
theorem exists_extinction_level {R M p : ℝ} (hR : 0 ≤ R) (hM : 0 < M) (hp : 2 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℝ → ℝ,
      (∀ k, 0 ≤ k → 0 ≤ Y k) → Y 0 ≤ M →
      (∀ k l, 0 ≤ k → k ≤ l → Y l ≤ Y k) →
      (∀ k l, 0 ≤ k → k < l → Y l ≤ R * Y k ^ (p - 1) / (l - k) ^ p) →
      Y K = 0 := by
  let θ : ℝ := (1 / 2 : ℝ) ^ (p / (p - 2))
  have hθ : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num)
    (div_pos (by linarith) (by linarith))
  let D := R * M ^ (p - 2)
  have hD : 0 ≤ D := mul_nonneg hR (Real.rpow_nonneg hM.le _)
  let T := (D / θ + 1) ^ (1 / p)
  have hbase : 0 < D / θ + 1 := by positivity
  have hT : 0 < T := Real.rpow_pos_of_pos hbase _
  have hTp : T ^ p = D / θ + 1 := by
    dsimp [T]
    rw [one_div, Real.rpow_inv_rpow hbase.le (by linarith : p ≠ 0)]
  let A := R * T ^ (-p)
  let B : ℝ := (1 / 2 : ℝ) ^ (-p)
  have hA : 0 ≤ A := mul_nonneg hR (Real.rpow_nonneg hT.le _)
  have hB : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
  have hsmall : A * M ^ ((p - 1) - 1) ≤ θ := by
    have he : A * M ^ ((p - 1) - 1) = D / T ^ p := by
      dsimp [A, D]
      rw [Real.rpow_neg hT.le, show p - 1 - 1 = p - 2 by ring]
      ring
    rw [he, hTp]
    apply (div_le_iff₀ hbase).mpr
    have heq : θ * (D / θ + 1) = D + θ := by field_simp
    rw [heq]
    linarith
  have hamp : B * θ ^ ((p - 1) - 1) ≤ 1 := by
    have hexp : p / (p - 2) * (p - 1 - 1) = p := by
      have hn : p - 2 ≠ 0 := by linarith
      field_simp [hn]
      ring
    dsimp [B, θ]
    rw [← Real.rpow_mul (by norm_num), hexp, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  refine ⟨2 * T, by positivity, ?_⟩
  intro Y hY hstart hmono hstep
  let k := fun j : ℕ => 2 * T * (1 - (1 / 2 : ℝ) ^ j)
  have hk (j : ℕ) : 0 ≤ k j :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))
  have hklt (j : ℕ) : k j < 2 * T := by
    dsimp [k]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j]
  have hgap (j : ℕ) : k (j + 1) - k j = T * (1 / 2 : ℝ) ^ j := by
    dsimp [k]
    rw [pow_succ]
    ring
  have hkstep (j : ℕ) : k j < k (j + 1) := by
    have hh : 0 < T * (1 / 2 : ℝ) ^ j := mul_pos hT (pow_pos (by norm_num) _)
    linarith [hgap j]
  have hrec (j : ℕ) : Y (k (j + 1)) ≤ A * B ^ j * Y (k j) ^ (p - 1) := by
    have hh := hstep (k j) (k (j + 1)) (hk j) (hkstep j)
    rw [hgap] at hh
    have hpow : ((1 / 2 : ℝ) ^ j) ^ (-p) = B ^ j := by
      dsimp [B]
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (j : ℝ) (-p),
        Real.rpow_mul_natCast (by norm_num)]
    have he : R * Y (k j) ^ (p - 1) / (T * (1 / 2 : ℝ) ^ j) ^ p =
        A * B ^ j * Y (k j) ^ (p - 1) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg (mul_nonneg hT.le (pow_nonneg (by norm_num) _)),
        Real.mul_rpow hT.le (pow_nonneg (by norm_num) _), hpow]
      dsimp [A]
      ring
    exact hh.trans_eq he
  have hdec := power_recurrence_decay (fun j => hY (k j) (hk j)) hA hB hM hθ
    (by linarith : 1 < p - 1) (by simpa [k] using hstart) hsmall hamp hrec
  apply eq_zero_of_le_geometric (hY (2 * T) (by positivity)) hθ.le hθ1
  intro j
  exact (hmono (k j) (2 * T) (hk j) (hklt j).le).trans (hdec j)

end RegularPointCoordinates

end

end OAI
