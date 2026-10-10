import OAI.NumberTheory.Ostmann.Construction.TransferGraphRows

namespace OAI

/-! # Identification of every surviving local factor with the new graph phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The erased pivot is represented only by its total integer. Its outgoing
row has already been removed by Cauchy--Schwarz. -/
noncomputable def retainedGraphRow {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option I → Option I → ℤ)
    (i : I) (P : ZMod p) (q : I → ZMod p) : ℂ :=
  χ P ^ b (some i) none * ∏ j, χ (q j) ^ b (some i) (some j)

noncomputable def updatedGraphRow {H Y : Type*} [Fintype H] [Fintype Y] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (i : (Bool × H) ⊕ Y) (L R : H → ZMod p) (U : Y → ZMod p) : ℂ :=
  ∏ j, χ (transferredLabels L R U j) ^ transferredGraph b i j

/-- The complete retained factor at a left-slot prime becomes the left
local factor of the updated directed graph. -/
theorem transfer_left_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (h : H)
    (P D v s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p) (ν : ℂ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hR : (∏ k, R k) ≠ 0) (hs : s ≠ 0)
    (hrel : v * (∏ k, R k) = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) * ν *
      retainedGraphRow χ b (.inl h) P (Sum.elim L U) =
    ZMod.stdAddChar (t * (s / ((∏ k, R k) * D))) *
      (ν * χ (v / s) ^ b (some (.inl h)) none) *
      updatedGraphRow χ b (.inl (true, h)) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, transferredGraph_left_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have he := transfer_left_row χ P D v s t R ν
    (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k)))
    (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)))
    (b (some (.inl h)) none) hP hD hR hs hrel
  calc
    _ = ZMod.stdAddChar (t * (v / (P * D))) * ν * χ P ^ b (some (.inl h)) none *
        (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k))) *
        ∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)) := by ring
    _ = _ := by rw [he]; ring

theorem transfer_right_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (h : H)
    (P D w s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p) (ν : ℂ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hL : (∏ k, L k) ≠ 0) (hs : s ≠ 0)
    (hrel : -w * (∏ k, L k) = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D))) * ν *
      retainedGraphRow χ b (.inl h) P (Sum.elim R U)) =
    ZMod.stdAddChar (t * (s / ((∏ k, L k) * D))) *
      (conj ν * χ (-w / s) ^ (-b (some (.inl h)) none)) *
      updatedGraphRow χ b (.inl (false, h)) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, transferredGraph_right_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have he := transfer_right_row χ P D w s t L ν
    (∏ k, χ (R k) ^ b (some (.inl h)) (some (.inl k)))
    (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)))
    (b (some (.inl h)) none) hP hD hL hs hrel
  calc
    _ = conj (ZMod.stdAddChar (t * (w / (P * D))) * ν * χ P ^ b (some (.inl h)) none *
        (∏ k, χ (R k) ^ b (some (.inl h)) (some (.inl k))) *
        ∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y))) := by congr 1; ring
    _ = _ := by
      rw [he]
      simp only [map_prod (starRingEnd ℂ), conjugate_character_power]
      ring

/-- The common outside row has unit modulus on the actual coprime support;
the self-edge is allowed because its exponent is zero. -/
theorem transfer_common_row_norm_one {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y)
    (P : ZMod p) (U : Y → ZMod p) (hP : IsUnit P)
    (hU : ∀ z, z ≠ y → IsUnit (U z)) (hb : b (some (.inr y)) (some (.inr y)) = 0) :
    ‖χ P ^ b (some (.inr y)) none *
      ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))‖ = 1 := by
  classical
  obtain ⟨u, hu⟩ := hP
  rw [norm_mul, ← hu, norm_zpow, χ.unit_norm_eq_one, one_zpow, one_mul, norm_prod]
  apply Finset.prod_eq_one
  intro z _
  by_cases hz : z = y
  · subst z
    rw [hb, zpow_zero, norm_one]
  · obtain ⟨a, ha⟩ := hU z hz
    rw [← ha, norm_zpow, χ.unit_norm_eq_one, one_zpow]

/-- The shared-slot row cancels its entire common part. Its new incoming
powers are exactly those prescribed by `transferredGraph`. -/
theorem transfer_outside_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y)
    (P LP RP D v w s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p)
    (νv νw : ℂ) (hP : P ≠ 0) (hL : LP ≠ 0) (hR : RP ≠ 0) (hD : D ≠ 0)
    (hcommon : ‖χ P ^ b (some (.inr y)) none *
      ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))‖ = 1)
    (hrel : v * RP - w * LP = s * P) :
    (ZMod.stdAddChar (t * (v / (P * LP * D))) * νv *
      retainedGraphRow χ b (.inr y) P (Sum.elim L U)) *
      conj (ZMod.stdAddChar (t * (w / (P * RP * D))) * νw *
        retainedGraphRow χ b (.inr y) P (Sum.elim R U)) =
    ZMod.stdAddChar (t * (s / (LP * RP * D))) * (νv * conj νw) *
      updatedGraphRow χ b (.inr y) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, transferredGraph_outside_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  let C := χ P ^ b (some (.inr y)) none *
    ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))
  let SL := ∏ k, χ (L k) ^ b (some (.inr y)) (some (.inl k))
  let SR := ∏ k, χ (R k) ^ b (some (.inr y)) (some (.inl k))
  have he := transfer_outside_row P LP RP D v w s t νv νw C SL SR hP hL hR hD hcommon hrel
  calc
    _ = (ZMod.stdAddChar (t * (v / (P * LP * D))) * νv * C * SL) *
        conj (ZMod.stdAddChar (t * (w / (P * RP * D))) * νw * C * SR) := by
      dsimp [C, SL, SR]
      apply congrArg₂ (fun a b : ℂ => a * conj b) <;> ring
    _ = _ := by
      rw [he]
      dsimp [SL, SR]
      simp only [map_prod (starRingEnd ℂ), conjugate_character_power]
      ring

end Ostmann

end OAI
