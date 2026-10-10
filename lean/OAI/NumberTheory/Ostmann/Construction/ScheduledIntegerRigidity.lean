import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledCutoffs
import OAI.NumberTheory.Ostmann.Construction.InitialMovingTemplateProduct

namespace OAI

/-! # Actual product separation on the retained initial-coefficient support -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def scheduledPivotBound (G : ℝ) (cs : List ℕ) (n : ℕ) : ℕ :=
  ⌈Real.exp (G + 1 + (2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1))⌉₊

noncomputable def scheduledProductRounding (width : ℝ) (cs : List ℕ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (width + 14 + 4 * cs.length)

theorem scheduledPivotBound_upper (G width : ℝ) (cs : List ℕ) (n : ℕ)
    (hG : 1 ≤ G) (hwidth : 0 ≤ width) :
    (scheduledPivotBound G cs n : ℝ) ≤
      Real.exp (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n +
        scheduledProductRounding width cs n) := by
  let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n
  let Z := G + 1 + (2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1)
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    positivity
  have hceil : (scheduledPivotBound G cs n : ℝ) ≤ 2 * Real.exp Z := by
    have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg Z)).le
    have hz := Real.one_le_exp hZ
    change (⌈Real.exp Z⌉₊ : ℝ) ≤ _
    linarith
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmargin : Real.log 2 + Z ≤ T + scheduledProductRounding width cs n := by
    dsimp only [T, Z, scheduledProductRounding]
    rw [selected_cell_pivot_exponent]
    have hw := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hwidth
    have hl := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity)
      (Nat.cast_nonneg cs.length (α := ℝ))
    nlinarith only [hlog, hr, hw, hl]
  apply hceil.trans
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  exact Real.exp_le_exp.mpr hmargin

theorem scheduled_retained_product_exponent (G Y cb cd width Dlog : ℝ)
    (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      (G - 1 + (∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 : ℝ) ^ n * (2 * cb - 2)) =
      (2 : ℝ) ^ n * (2 * cd - Dlog + width + 10 + 4 * (cs.drop (n + 1)).length) := by
  rw [selectedProductExponent_eq, selected_cell_pivot_exponent, nat_cell_drop_sum cs n,
    scheduledSmallLower_sum]
  have hs := list_sum_sub_one ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ)))
  simp only [List.map_map, Function.comp_def, List.length_map] at hs
  rw [hs]
  push_cast
  ring

theorem scheduled_retained_product_rounding (G Y cb cd width Dlog : ℝ)
    (top : ℕ) (cs : List ℕ) (n : ℕ) (hD : 2 * cd - 2 ≤ Dlog) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      scheduledProductRounding width cs n ≤
      G - 1 + (∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 : ℝ) ^ n * (2 * cb - 2) := by
  have he := scheduled_retained_product_exponent G Y cb cd width Dlog top cs n
  have hlen : ((cs.drop (n + 1)).length : ℝ) ≤ cs.length := by
    exact_mod_cast (show (cs.drop (n + 1)).length ≤ cs.length by simp only [List.length_drop]; omega)
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hh := mul_le_mul_of_nonneg_left (show
    2 * cd - Dlog + width + 10 + 4 * (cs.drop (n + 1)).length ≤ width + 14 + 4 * cs.length by
      linarith only [hD, hlen]) hr
  unfold scheduledProductRounding
  linarith only [he, hh]

theorem scheduled_original_retained_product_lower {A I : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d top : ℕ) (cs : List ℕ) (cb cd G Y width Dlog : ℝ)
    (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (n : ℕ) (hn : n < cs.length)
    (u : TreeLeafIndex n × Fin 4 → A)
    (right : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b) → A)
    (p XR : ℕ) (w : ℤ) (hXR : Real.exp (G - 1) ≤ (XR : ℝ))
    (hD : 2 * cd - 2 ≤ Dlog)
    (hlower : ∀ j, Real.exp (scheduledSmallLower top (cs.drop (n + 1)) n j) ≤
      (value (right (j.1, .inl j.2)) : ℝ))
    (hcoeff : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d (initialSmallCellList top cs).length cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ (fun _ => G) n
      (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b) w
      (movingRestoreSample n (scheduledSmallLength (cs.drop (n + 1))) (b + b) u right) p XR ≠ 0) :
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    Real.exp (movingProductExponent T W n - T n - scheduledProductRounding width cs n) ≤
      ((XR * ∏ i, value (right i) : ℕ) : ℝ) := by
  intro T W
  have hprod := movingTemplateCoefficient_original_initial_full_lower value hvalue b d
    (initialSmallCellList top cs).length cb cd sl sr fallback q g Dq S ψ X lo hi outside μ
    childBound pivotBound V φ (fun _ => G) n (scheduledSmallLength (cs.drop (n + 1))) w
    u right (scheduled_drop_length_balance top cs n hn) _ hlower p XR hcoeff
  have hround := scheduled_retained_product_rounding G Y cb cd width Dlog top cs n hD
  apply (Real.exp_le_exp.mpr hround).trans
  rw [Real.exp_add, Real.exp_add, Nat.cast_mul]
  push_cast at hprod
  simpa only [Real.exp_add, Nat.cast_prod, mul_assoc] using
    mul_le_mul hXR hprod (Real.exp_nonneg _) (Nat.cast_nonneg XR)

theorem scheduled_integer_rigidity (G Y cb cd width Dlog m : ℝ)
    (top : ℕ) (cs : List ℕ) (n R : ℕ)
    (hG : 1 ≤ G) (hwidth : 0 ≤ width)
    (hbudget : 40 * (width + 14 + 4 * cs.length) + 20 * Real.log 2 < m)
    (hR : Real.exp (
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      scheduledProductRounding width cs n) ≤ (R : ℝ))
    (hmargin : (1 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
          (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
        2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n) -
      movingProductFrequencyExponent
        (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) (Y - Dlog) (m / 4) n) :
    2 * scheduledPivotBound G cs n *
      movingProductNaturalCutoff
        (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) (Y - Dlog) (m / 4) n < R := by
  apply movingProductNaturalCutoff_rigidity _ _ _ _ (scheduledProductRounding width cs n)
    n (scheduledPivotBound G cs n) R (scheduledPivotBound_upper G width cs n hG hwidth) hR
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 < (2 : ℝ) ^ n := by positivity
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_lt_mul_of_pos_left hbudget hr0
  have hl := mul_le_mul_of_nonneg_right hr hlog
  unfold scheduledProductRounding
  nlinarith only [hh, hl, hmargin]

end Ostmann

end OAI
