import OAI.Analysis.MarkovType.JConvexityBasic
import OAI.Analysis.MarkovType.JConvexityScalarSquares
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem square_le_square {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  have hb : 0 ≤ b := ha.trans hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb ha)]

theorem cutSum_seminorm_le_sum (p : Seminorm ℝ X) {n : ℕ}
    (x : Fin n → X) (r : Fin n) : p (cutSum x r) ≤ ∑ j, p (x j) := by
  have hfinite : ∀ s : Finset (Fin n),
      p (∑ j ∈ s, cutSign r j • x j) ≤ ∑ j ∈ s, p (x j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      calc
        p (cutSign r j • x j + ∑ k ∈ s, cutSign r k • x k)
            ≤ p (cutSign r j • x j) + p (∑ k ∈ s, cutSign r k • x k) :=
          map_add_le_add p _ _
        _ ≤ p (x j) + ∑ k ∈ s, p (x k) := by
          rw [map_smul_eq_mul, norm_cutSign, one_mul]
          exact add_le_add le_rfl ih
  exact hfinite Finset.univ

theorem JConvexWitness.scaled {p : Seminorm ℝ X} {n : ℕ} {δ R : ℝ}
    (h : JConvexWitness p n δ) (hR : 0 < R) (x : Fin n → X)
    (hx : ∀ j, p (x j) ≤ R) :
    ∃ r : Fin n, p (cutSum x r) ≤ (n : ℝ) * (1 - δ) * R := by
  have hi : 0 < R⁻¹ := inv_pos.mpr hR
  have hunit : ∀ j, p (R⁻¹ • x j) ≤ 1 := by
    intro j
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hi]
    calc
      R⁻¹ * p (x j) ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hx j) hi.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hR)
  obtain ⟨r, hr⟩ := h (fun j => R⁻¹ • x j) hunit
  have hr' : R⁻¹ * p (cutSum x r) ≤ (n : ℝ) * (1 - δ) := by
    simpa only [cutSum_smul, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hi] using hr
  refine ⟨r, ?_⟩
  calc
    p (cutSum x r) = R * (R⁻¹ * p (cutSum x r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul]
    _ ≤ R * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr' hR.le
    _ = (n : ℝ) * (1 - δ) * R := by ring

private theorem normalized_cut_square_drop {p : Seminorm ℝ X} {n : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hδ1 : δ < 1) (hJ : JConvexWitness p n δ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧
      ∀ x : Fin n → X, (∑ j, p (x j)) = (n : ℝ) →
        ∃ r : Fin n,
          p (cutSum x r) ^ 2 ≤ κ * ((n : ℝ) * ∑ j, p (x j) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdhalf : 0 < δ / 2 := by positivity
  have hden : 0 < (n : ℝ) + (δ / 2) ^ 2 := by positivity
  let β : ℝ := (n : ℝ) / ((n : ℝ) + (δ / 2) ^ 2)
  let κ : ℝ := max ((1 - δ / 2) ^ 2) β
  have hβ0 : 0 ≤ β := div_nonneg hnR.le hden.le
  have hβ1 : β < 1 := by
    apply (div_lt_one hden).mpr
    have hd2 : 0 < (δ / 2) ^ 2 := by positivity
    linarith
  have hbase0 : 0 ≤ 1 - δ / 2 := by linarith
  have hbase1 : (1 - δ / 2) ^ 2 < 1 := by
    have hprod : 0 < (δ / 2) * (2 - δ / 2) :=
      mul_pos hdhalf (by linarith)
    nlinarith
  have hκ0 : 0 ≤ κ := (sq_nonneg (1 - δ / 2)).trans (le_max_left _ _)
  have hκ1 : κ < 1 := max_lt hbase1 hβ1
  refine ⟨κ, hκ0, hκ1, ?_⟩
  intro x hx
  let Q : ℝ := ∑ j, p (x j) ^ 2
  have hQ : (n : ℝ) ≤ Q := card_le_sum_sq_of_sum_eq (fun j => p (x j)) hx
  have hQ0 : 0 ≤ Q := hnR.le.trans hQ
  have hnnQ : (n : ℝ) ^ 2 ≤ (n : ℝ) * Q := by
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hQ)]
  by_cases hclose : ∀ j, p (x j) ≤ 1 + δ / 2
  · obtain ⟨r, hr⟩ := hJ.scaled (by linarith : 0 < 1 + δ / 2) x hclose
    have hfactor : (1 - δ) * (1 + δ / 2) ≤ 1 - δ / 2 := by
      nlinarith [sq_nonneg δ]
    have hrsmall : p (cutSum x r) ≤ (n : ℝ) * (1 - δ / 2) := by
      calc
        p (cutSum x r) ≤ (n : ℝ) * (1 - δ) * (1 + δ / 2) := hr
        _ = (n : ℝ) * ((1 - δ) * (1 + δ / 2)) := by ring
        _ ≤ (n : ℝ) * (1 - δ / 2) := mul_le_mul_of_nonneg_left hfactor hnR.le
    refine ⟨r, ?_⟩
    calc
      p (cutSum x r) ^ 2 ≤ ((n : ℝ) * (1 - δ / 2)) ^ 2 :=
        square_le_square (apply_nonneg p _) hrsmall
      _ = (1 - δ / 2) ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ (1 - δ / 2) ^ 2 * ((n : ℝ) * Q) :=
        mul_le_mul_of_nonneg_left hnnQ (sq_nonneg _)
      _ ≤ κ * ((n : ℝ) * Q) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hnR.le hQ0)
  · obtain ⟨k, hk⟩ := not_forall.mp hclose
    have hk' : 1 + δ / 2 ≤ p (x k) := (lt_of_not_ge hk).le
    have hQgap : (n : ℝ) + (δ / 2) ^ 2 ≤ Q :=
      card_add_sq_le_sum_sq_of_one_add_le (fun j => p (x j)) hx k hdhalf.le hk'
    let r : Fin n := ⟨0, hn⟩
    have hr : p (cutSum x r) ≤ (n : ℝ) := by
      simpa only [hx] using cutSum_seminorm_le_sum p x r
    refine ⟨r, ?_⟩
    calc
      p (cutSum x r) ^ 2 ≤ (n : ℝ) ^ 2 := square_le_square (apply_nonneg p _) hr
      _ = β * ((n : ℝ) * ((n : ℝ) + (δ / 2) ^ 2)) := by
        dsimp [β]
        field_simp [ne_of_gt hden]

      _ ≤ β * ((n : ℝ) * Q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hQgap hnR.le) hβ0
      _ ≤ κ * ((n : ℝ) * Q) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hnR.le hQ0)

theorem JConvex.squareAverage {p : Seminorm ℝ X} (h : JConvex p) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ x : Fin n → X,
        (n : ℝ)⁻¹ * (∑ r, p (cutSum x r) ^ 2)
          ≤ α ^ 2 * (n : ℝ) * ∑ j, p (x j) ^ 2 := by
  obtain ⟨n, hn, δ, hδ, hδ1, hJ⟩ := h
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨κ, hκ0, hκ1, hdrop⟩ := normalized_cut_square_drop hnpos hδ hδ1 hJ
  let a2 : ℝ := ((n : ℝ) - 1 + κ) / (n : ℝ)
  have ha20 : 0 ≤ a2 := div_nonneg (by linarith) hnR.le
  have ha21 : a2 < 1 := by
    apply (div_lt_one hnR).mpr
    linarith
  let α : ℝ := Real.sqrt a2
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = a2 := Real.sq_sqrt ha20
  have hα1 : α < 1 := by nlinarith [sq_nonneg (α - 1)]
  have hnormalized : ∀ x : Fin n → X, (∑ j, p (x j)) = (n : ℝ) →
      (∑ r, p (cutSum x r) ^ 2) ≤ α ^ 2 * (n : ℝ) ^ 2 * ∑ j, p (x j) ^ 2 := by
    intro x hx
    let Q : ℝ := ∑ j, p (x j) ^ 2
    have hQ : (n : ℝ) ≤ Q := card_le_sum_sq_of_sum_eq (fun j => p (x j)) hx
    have hnnQ : (n : ℝ) ^ 2 ≤ (n : ℝ) * Q := by
      nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hQ)]
    have heach : ∀ r, p (cutSum x r) ^ 2 ≤ (n : ℝ) * Q := by
      intro r
      have hr : p (cutSum x r) ≤ (n : ℝ) := by
        simpa only [hx] using cutSum_seminorm_le_sum p x r
      exact (square_le_square (apply_nonneg p _) hr).trans hnnQ
    obtain ⟨r, hr⟩ := hdrop x hx
    have hsum := sum_le_card_sub_one_mul_add
      (fun r => p (cutSum x r) ^ 2) r heach hr
    calc
      (∑ r, p (cutSum x r) ^ 2)
          ≤ ((n : ℝ) - 1) * ((n : ℝ) * Q) + κ * ((n : ℝ) * Q) := hsum
      _ = α ^ 2 * (n : ℝ) ^ 2 * Q := by
        rw [hαsq]
        dsimp [a2]
        field_simp [ne_of_gt hnR]

  have hall : ∀ x : Fin n → X,
      (∑ r, p (cutSum x r) ^ 2) ≤ α ^ 2 * (n : ℝ) ^ 2 * ∑ j, p (x j) ^ 2 := by
    intro x
    let L : ℝ := ∑ j, p (x j)
    have hL0 : 0 ≤ L := Finset.sum_nonneg (fun j _ => apply_nonneg p _)
    by_cases hL : L = 0
    · have hx0 : ∀ j, p (x j) = 0 := by
        intro j
        have hj : p (x j) ≤ L :=
          Finset.single_le_sum (fun k _ => apply_nonneg p (x k)) (Finset.mem_univ j)
        exact le_antisymm (by simpa only [hL] using hj) (apply_nonneg p _)
      have hc0 : ∀ r, p (cutSum x r) = 0 := by
        intro r
        apply le_antisymm
        · have hc := cutSum_seminorm_le_sum p x r
          simpa only [hx0, Finset.sum_const_zero] using hc
        · exact apply_nonneg p _
      simp only [hx0, hc0, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
        mul_zero, le_refl]
    · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
      let a : ℝ := (n : ℝ) / L
      have ha : 0 < a := div_pos hnR hLpos
      let y : Fin n → X := fun j => a • x j
      have hpsum : ∀ j, p (y j) = a * p (x j) := by
        intro j
        dsimp [y]
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha]
      have hy : (∑ j, p (y j)) = (n : ℝ) := by
        simp_rw [hpsum]
        rw [← Finset.mul_sum]
        change a * L = (n : ℝ)
        dsimp [a]
        exact div_mul_cancel₀ _ (ne_of_gt hLpos)
      have hleft : (∑ r, p (cutSum y r) ^ 2) = a ^ 2 * ∑ r, p (cutSum x r) ^ 2 := by
        dsimp [y]
        simp_rw [cutSum_smul, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
        rw [Finset.mul_sum]
      have hright : (∑ j, p (y j) ^ 2) = a ^ 2 * ∑ j, p (x j) ^ 2 := by
        simp_rw [hpsum, mul_pow]
        rw [Finset.mul_sum]
      have hb := hnormalized y hy
      rw [hleft, hright] at hb
      have hb' : a ^ 2 * (∑ r, p (cutSum x r) ^ 2) ≤
          a ^ 2 * (α ^ 2 * (n : ℝ) ^ 2 * ∑ j, p (x j) ^ 2) := by
        convert hb using 1 ; ring
      exact le_of_mul_le_mul_left hb' (by positivity : 0 < a ^ 2)
  refine ⟨n, hn, α, hα0, hα1, ?_⟩
  intro x
  calc
    (n : ℝ)⁻¹ * (∑ r, p (cutSum x r) ^ 2)
        ≤ (n : ℝ)⁻¹ * (α ^ 2 * (n : ℝ) ^ 2 * ∑ j, p (x j) ^ 2) :=
      mul_le_mul_of_nonneg_left (hall x) (inv_nonneg.mpr hnR.le)
    _ = α ^ 2 * (n : ℝ) * ∑ j, p (x j) ^ 2 := by
      field_simp [ne_of_gt hnR]

end MarkovSuperreflexivity

end OAI
