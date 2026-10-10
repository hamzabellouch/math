import OAI.NumberTheory.TwoPoint.Walks.FiveColorOrientation
import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction

namespace OAI

/-! Recover a directed short-range kernel from ten tests of its symmetric kernel. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev ForwardColorCode := Fin 5 × Fin 2

abbrev sourceColor (D : ℤ) (c : ForwardColorCode) (x : ℤ) : Prop :=
  intervalColor D x = c.1.val

abbrev targetColor (D : ℤ) (c : ForwardColorCode) (y : ℤ) : Prop :=
  intervalColor D y = ((c.1.val : ℤ) + c.2.val + 1) % 5

lemma color_test_sum (D x y : ℤ) (z : ℂ) :
    (∑ c : ForwardColorCode, if sourceColor D c x ∧ targetColor D c y then z else 0) =
      if forwardColorPair D x y then z else 0 := by
  have hfinite (a b : ℤ) (ha : 0 ≤ a ∧ a < 5) (hb : 0 ≤ b ∧ b < 5) :
      (∑ c : ForwardColorCode,
        if a = c.1.val ∧ b = ((c.1.val : ℤ) + c.2.val + 1) % 5 then z else 0) =
      if (b - a) % 5 = 1 ∨ (b - a) % 5 = 2 then z else 0 := by
    rcases ha with ⟨ha0, ha5⟩
    rcases hb with ⟨hb0, hb5⟩
    interval_cases a <;> interval_cases b <;>
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hleft :
      (∑ c : ForwardColorCode, if sourceColor D c x ∧ targetColor D c y then z else 0) =
      ∑ c : ForwardColorCode, if intervalColor D x = c.1.val ∧
        intervalColor D y = ((c.1.val : ℤ) + c.2.val + 1) % 5 then z else 0 := by
    apply sum_congr rfl
    intro c _
    rfl
  have hright : (if forwardColorPair D x y then z else 0) =
      if (intervalColor D y - intervalColor D x) % 5 = 1 ∨
        (intervalColor D y - intervalColor D x) % 5 = 2 then z else 0 := by
    unfold forwardColorPair
    split_ifs <;> rfl
  rw [hleft, hright]
  exact hfinite _ _ (intervalColor_bounds D x) (intervalColor_bounds D y)

noncomputable def sourceColorFunction {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (F : V → ℂ) : V → ℂ :=
  fun i => if sourceColor D c (site i) then F i else 0

noncomputable def targetColorFunction {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (G : V → ℂ) : V → ℂ :=
  fun i => if targetColor D c (site i) then G i else 0

lemma sourceColorFunction_norm_le {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (F : V → ℂ) (hF : ∀ i, ‖F i‖ ≤ 1) (i : V) :
    ‖sourceColorFunction D site c F i‖ ≤ 1 := by
  unfold sourceColorFunction
  split_ifs
  · exact hF i
  · simp

lemma targetColorFunction_norm_le {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (G : V → ℂ) (hG : ∀ i, ‖G i‖ ≤ 1) (i : V) :
    ‖targetColorFunction D site c G i‖ ≤ 1 := by
  unfold targetColorFunction
  split_ifs
  · exact hG i
  · simp

theorem five_color_bilinear_identity {V : Type*} [Fintype V]
    (D : ℤ) (hD : 0 < D) (site : V → ℤ) (K : V → V → ℂ)
    (hK : ∀ i j, K i j ≠ 0 → D ≤ site j - site i ∧ site j - site i < 2 * D)
    (F G : V → ℂ) :
    (∑ c : ForwardColorCode, ∑ i, ∑ j,
      sourceColorFunction D site c F i * targetColorFunction D site c G j * (K i j + K j i)) =
        ∑ i, ∑ j, F i * G j * K i j := by
  have hp (i j : V) :
      (∑ c : ForwardColorCode,
        sourceColorFunction D site c F i * targetColorFunction D site c G j * (K i j + K j i)) =
          F i * G j * K i j := by
    have he (c : ForwardColorCode) :
        sourceColorFunction D site c F i * targetColorFunction D site c G j * (K i j + K j i) =
        if sourceColor D c (site i) ∧ targetColor D c (site j) then
          F i * G j * (K i j + K j i) else 0 := by
      unfold sourceColorFunction targetColorFunction
      split_ifs <;> simp_all
    simp only [he, color_test_sum]
    by_cases hij : K i j = 0
    · rw [hij, zero_add, mul_zero]
      by_cases hji : K j i = 0
      · simp [hji]
      · rw [ite_eq_right (short_shift_not_reverse_colors D (site j) (site i) hD
          (hK j i hji).1 (hK j i hji).2)]
    · have hforward := short_shift_forward_colors D (site i) (site j) hD
        (hK i j hij).1 (hK i j hij).2
      have hji : K j i = 0 := by
        by_contra hji
        have hab := hK i j hij
        have hba := hK j i hji
        omega
      simp [hforward, hji]
  calc
    _ = ∑ i, ∑ j, ∑ c : ForwardColorCode,
        sourceColorFunction D site c F i * targetColorFunction D site c G j * (K i j + K j i) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by simp only [hp]

theorem five_color_bilinear_bound {V : Type*} [Fintype V]
    (D : ℤ) (hD : 0 < D) (site : V → ℤ) (K : V → V → ℂ)
    (hK : ∀ i j, K i j ≠ 0 → D ≤ site j - site i ∧ site j - site i < 2 * D)
    (F G : V → ℂ) (C : ℝ)
    (htest : ∀ c : ForwardColorCode,
      ‖∑ i, ∑ j, sourceColorFunction D site c F i *
        targetColorFunction D site c G j * (K i j + K j i)‖ ≤ C) :
    ‖∑ i, ∑ j, F i * G j * K i j‖ ≤ 10 * C := by
  rw [← five_color_bilinear_identity D hD site K hK F G]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c : ForwardColorCode, C := sum_le_sum (fun c _ => htest c)
    _ = _ := by simp [ForwardColorCode]

end TwoPointCorrelations

end OAI
