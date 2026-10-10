import OAI.Geometry.HeilbronnTriangle.LatticeReciprocal

namespace OAI


namespace Problem355.NormalFiberCount

theorem card_le_sum_fiber_bounds {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β) (bound : β → ℝ)
    (hf : ∀ x ∈ S, f x ∈ Y)
    (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound y) :
    (S.card : ℝ) ≤ ∑ y ∈ Y, bound y := by
  classical
  have hcard := Finset.card_eq_sum_card_fiberwise hf
  calc
    (S.card : ℝ) = ∑ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := Finset.sum_le_sum hbound

theorem card_le_card_mul_fiber_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β) (bound : ℝ)
    (hf : ∀ x ∈ S, f x ∈ Y)
    (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound) :
    (S.card : ℝ) ≤ (Y.card : ℝ) * bound := by
  simpa using card_le_sum_fiber_bounds S Y f (fun _ => bound) hf hbound

theorem card_triples_le_mul {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) (Y : Finset β) (Z : Finset γ)
    (B₁ B₂ B₃ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hY : (Y.card : ℝ) ≤ B₂) (hZ : (Z.card : ℝ) ≤ B₃)
    (hproj : ∀ x ∈ S, x.2.1 ∈ Y ∧ x.2.2 ∈ Z)
    (hfirst : ∀ y ∈ Y, ∀ z ∈ Z,
      ((S.filter (fun x => x.2 = (y, z))).card : ℝ) ≤ B₁) :
    (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
  have hcount := card_le_card_mul_fiber_bound S (Y.product Z)
    (fun x => x.2) B₁ (fun x hx => Finset.mem_product.mpr (hproj x hx))
    (fun yz hyz => hfirst yz.1 (Finset.mem_product.mp hyz).1
      yz.2 (Finset.mem_product.mp hyz).2)
  have hprod : ((Y.product Z).card : ℝ) = (Y.card : ℝ) * (Z.card : ℝ) := by
    exact_mod_cast Finset.card_product Y Z
  have hcount' : (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := by
    rwa [hprod] at hcount
  calc
    (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := hcount'
    _ ≤ B₂ * B₃ * B₁ := by
      apply mul_le_mul_of_nonneg_right _ hB₁
      exact mul_le_mul hY hZ (Nat.cast_nonneg _) hB₂
    _ = B₁ * B₂ * B₃ := by ring

theorem count_le_log_of_normal_fibers {α : Type*}
    (S : Finset α) (Y : Finset (Fin 3 → ℤ)) (normal : α → Fin 3 → ℤ)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hnormal : ∀ x ∈ S, normal x ∈ Y)
    (hY : ∀ y ∈ Y, y ≠ 0 ∧ ‖LatticeBox.realVector y‖ ≤ R)
    (hfiber : ∀ y ∈ Y,
      ((S.filter (fun x => normal x = y)).card : ℝ) ≤
        C / ‖LatticeBox.realVector y‖ ^ 3) :
    (S.card : ℝ) ≤ C * ((125 / Real.log 2) * Real.log (2 * R)) := by
  calc
    (S.card : ℝ) ≤ ∑ y ∈ Y, C / ‖LatticeBox.realVector y‖ ^ 3 :=
      card_le_sum_fiber_bounds S Y normal _ hnormal hfiber
    _ = C * ∑ y ∈ Y, 1 / ‖LatticeBox.realVector y‖ ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (LatticeBox.reciprocal_cube_sum_le_log hR Y hY) hC

theorem count_shortest_shell {α : Type*}
    (S : Finset α) (Y : Finset (Fin 3 → ℤ)) (normal : α → Fin 3 → ℤ)
    (C₀ C₁ R₁ R₂ R₃ U Z : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hR₃ : 0 ≤ R₃)
    (hU : 0 < U) (hZ : 0 < Z) (hUR : U ≤ R₃)
    (hnormal : ∀ x ∈ S, normal x ∈ Y)
    (hY : (Y.card : ℝ) ≤ C₀ * U ^ 4 * Z ^ 2)
    (hfiber : ∀ y ∈ Y,
      ((S.filter (fun x => normal x = y)).card : ℝ) ≤
        C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (U ^ 3 * Z ^ 2)) :
    (S.card : ℝ) ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by
  have hB : 0 ≤ C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (U ^ 3 * Z ^ 2) := by positivity
  calc
    (S.card : ℝ) ≤ (Y.card : ℝ) *
        (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (U ^ 3 * Z ^ 2)) :=
      card_le_card_mul_fiber_bound S Y normal _ hnormal hfiber
    _ ≤ (C₀ * U ^ 4 * Z ^ 2) *
        (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (U ^ 3 * Z ^ 2)) :=
      mul_le_mul_of_nonneg_right hY hB
    _ = (C₀ * C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃) * U := by
      field_simp
    _ ≤ (C₀ * C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃) * R₃ :=
      mul_le_mul_of_nonneg_left hUR (by positivity)
    _ = C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by ring

end Problem355.NormalFiberCount

end OAI
