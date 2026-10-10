import OAI.NumberTheory.Ostmann.Construction.TransferLocalPhases

namespace OAI

/-! # The bounded pivot row after grouping by v/H -/

namespace Ostmann

open scoped BigOperators

theorem character_zpow_norm_le_one {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (ε : ℤ) : ‖χ x ^ ε‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp only [norm_zpow, χ.unit_norm_eq_one, one_zpow, le_refl]
  · rw [χ.map_nonunit hx]
    by_cases he : ε = 0
    · simp [he]
    · simp [zero_zpow, he]

noncomputable def pivotLocalRow {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (t D Y u : ZMod p) (ε : ℤ) : ℂ :=
  ZMod.stdAddChar (t * (u * (D * Y)⁻¹)) * κ * χ (D * Y * u⁻¹) ^ ε

theorem pivotLocalRow_norm_le_one {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (hκ : ‖κ‖ ≤ 1) (t D Y u : ZMod p) (ε : ℤ) :
    ‖pivotLocalRow χ κ t D Y u ε‖ ≤ 1 := by
  rw [pivotLocalRow, norm_mul, norm_mul]
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  exact (mul_le_mul hκ (character_zpow_norm_le_one χ _ ε)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The complete outgoing local pivot factor sees the other active product H
only through u = v/H. -/
theorem pivotLocalRow_eq {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (t D Y H v u : ZMod p) (ε : ℤ)
    (hD : D ≠ 0) (hY : Y ≠ 0) (hH : H ≠ 0) (hu : u ≠ 0) (hv : v = u * H) :
    ZMod.stdAddChar (t * (v / (D * Y * H))) * κ *
      (χ v ^ (-ε) * χ (D * Y * H) ^ ε) = pivotLocalRow χ κ t D Y u ε := by
  have hv0 : v ≠ 0 := by rw [hv]; exact mul_ne_zero hu hH
  have ha : v / (D * Y * H) = u / (D * Y) := by rw [hv]; field_simp
  have hr : v * (D * Y) = u * (D * Y * H) := by rw [hv]; ring
  have hc := transfer_left_regular_factor χ (D * Y * H) (D * Y) v u hv0 hu hr ε
  rw [ha, hc]
  change _ = ZMod.stdAddChar (t * (u / (D * Y))) * κ * χ (D * Y / u) ^ ε
  have hd : χ (D * Y / u) ^ ε = χ (D * Y) ^ ε * χ u ^ (-ε) := by
    rw [div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.inv_apply_eq_inv',
      mul_zpow, inv_zpow, zpow_neg]
  rw [hd]
  ring

noncomputable def pivotTupleRow {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i)) (κ : I → ℂ)
    (t D Y u : ∀ i, ZMod (p i)) (ε : I → ℤ) : ℂ :=
  ∏ i, pivotLocalRow (χ i) (κ i) (t i) (D i) (Y i) (u i) (ε i)

theorem pivotTupleRow_norm_le_one {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i)) (κ : I → ℂ)
    (hκ : ∀ i, ‖κ i‖ ≤ 1) (t D Y u : ∀ i, ZMod (p i)) (ε : I → ℤ) :
    ‖pivotTupleRow p χ κ t D Y u ε‖ ≤ 1 := by
  rw [pivotTupleRow, norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    (fun i _ => pivotLocalRow_norm_le_one _ _ (hκ i) _ _ _ _ _)

end Ostmann

end OAI
