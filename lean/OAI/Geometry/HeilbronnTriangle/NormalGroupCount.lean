import OAI.Geometry.HeilbronnTriangle.LatticeBox

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

theorem card_le_sum_card_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (r : α → β → Prop) [DecidableRel r]
    (hcover : ∀ a ∈ S, ∃ b ∈ T, r a b) :
    S.card ≤ ∑ b ∈ T, (S.filter (fun a => r a b)).card := by
  calc
    S.card ≤ (T.biUnion (fun b => S.filter (fun a => r a b))).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨b, hb, hab⟩ := hcover a ha
      exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
    _ ≤ ∑ b ∈ T, (S.filter (fun a => r a b)).card := Finset.card_biUnion_le

theorem normal_group_card_le {U Z C : ℝ} (hU : 1 ≤ U) (hC : 0 ≤ C)
    (P : (Fin 3 → ℤ) → Prop) (S : Finset (Fin 3 → ℤ))
    (hcover : ∀ y ∈ S, ∃ z : Fin 3 → ℤ,
      P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U ∧ dotProduct z y = 0)
    (hplane : ∀ z, P z → U ≤ ‖realVector z‖ → ‖realVector z‖ ≤ 2 * U →
      ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) ≤ C * U * Z ^ 2) :
    (S.card : ℝ) ≤ 125 * C * U ^ 4 * Z ^ 2 := by
  classical
  let T := (box 3 ⌊2 * U⌋₊).filter (fun z =>
    P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U)
  have hT : ∀ z ∈ T, P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hTcard : (T.card : ℝ) ≤ 125 * U ^ 3 :=
    card_le_of_norm_bound_twice hU T (fun z hz => (hT z hz).2.2)
  have hcoverT : ∀ y ∈ S, ∃ z ∈ T, dotProduct z y = 0 := by
    intro y hy
    obtain ⟨z, hzP, hzU, hz2U, hzy⟩ := hcover y hy
    refine ⟨z, Finset.mem_filter.mpr ⟨?_, hzP, hzU, hz2U⟩, hzy⟩
    apply mem_box.mpr
    intro i
    exact int_abs_le_floor ((abs_coord_le_norm z i).trans hz2U)
  have hnat := card_le_sum_card_cover S T (fun y z => dotProduct z y = 0) hcoverT
  have hreal : (S.card : ℝ) ≤
      ∑ z ∈ T, ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (S.card : ℝ) ≤ ∑ z ∈ T, ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) := hreal
    _ ≤ ∑ _z ∈ T, C * U * Z ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact hplane z (hT z hz).1 (hT z hz).2.1 (hT z hz).2.2
    _ = (T.card : ℝ) * (C * U * Z ^ 2) := by simp
    _ ≤ (125 * U ^ 3) * (C * U * Z ^ 2) := by
      apply mul_le_mul_of_nonneg_right hTcard
      positivity
    _ = 125 * C * U ^ 4 * Z ^ 2 := by ring

theorem normal_group_card_le_of_plane_estimate {U Z C : ℝ}
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (P : (Fin 3 → ℤ) → Prop) (S : Finset (Fin 3 → ℤ))
    (hcover : ∀ y ∈ S, ∃ z : Fin 3 → ℤ,
      P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U ∧ dotProduct z y = 0)
    (hplane : ∀ z, P z → U ≤ ‖realVector z‖ → ‖realVector z‖ ≤ 2 * U →
      ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) ≤
        C * (4 * U * Z) ^ 2 / ‖realVector z‖) :
    (S.card : ℝ) ≤ 2000 * C * U ^ 4 * Z ^ 2 := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hbound : (S.card : ℝ) ≤ 125 * (16 * C) * U ^ 4 * Z ^ 2 := by
    apply normal_group_card_le hU (by positivity) P S hcover
    intro z hzP hzU hz2U
    calc
      ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) ≤
          C * (4 * U * Z) ^ 2 / ‖realVector z‖ := hplane z hzP hzU hz2U
      _ ≤ C * (4 * U * Z) ^ 2 / U :=
        div_le_div_of_nonneg_left (by positivity) hUpos hzU
      _ = (16 * C) * U * Z ^ 2 := by field_simp; ring
  nlinarith [hbound]

end Problem355.LatticeBox

end

end OAI
