import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusOddCommutator

namespace OAI

/-! # Small high-frequency tails for the actual physical commutator -/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def expandingFrequencyLow (L R : ℝ) : FourierL2 →L[ℂ] FourierL2 :=
  let F : FourierL2 → FourierL2 := fun f =>
    ⟨fun n => if ‖n‖ < R * L then f n else 0, by
      apply (lp.memℓp f).mono'
      intro n
      split_ifs <;> simp⟩
  LinearMap.mkContinuous
    { toFun := F
      map_add' := by
        intro f g
        ext n
        change (if ‖n‖ < R * L then f n + g n else 0) =
          (if ‖n‖ < R * L then f n else 0) + (if ‖n‖ < R * L then g n else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c f
        ext n
        change (if ‖n‖ < R * L then c * f n else 0) = c * (if ‖n‖ < R * L then f n else 0)
        split_ifs <;> simp }
    1 (by
      intro f
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖if ‖n‖ < R * L then f n else 0‖ ≤ ‖f n‖
      split_ifs <;> simp)

@[simp] theorem expandingFrequencyLow_apply (L R : ℝ) (f : FourierL2) (n : frequencyLattice) :
    expandingFrequencyLow L R f n = if ‖n‖ < R * L then f n else 0 := rfl

noncomputable def expandingFrequencyHigh (L R : ℝ) : FourierL2 →L[ℂ] FourierL2 :=
  ContinuousLinearMap.id ℂ FourierL2 - expandingFrequencyLow L R

@[simp] theorem expandingFrequencyHigh_apply (L R : ℝ) (f : FourierL2) (n : frequencyLattice) :
    expandingFrequencyHigh L R f n = if ‖n‖ < R * L then 0 else f n := by
  change f n - (if ‖n‖ < R * L then f n else 0) = _
  split_ifs <;> simp

theorem expandingFrequencyHigh_norm_le (L R : ℝ) (f : FourierL2) :
    ‖expandingFrequencyHigh L R f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [expandingFrequencyHigh_apply]
  split_ifs <;> simp

theorem expandingFrequency_split (L R : ℝ) (f : FourierL2) :
    f = expandingFrequencyLow L R f + expandingFrequencyHigh L R f := by
  ext n
  simp only [lp.coeFn_add, Pi.add_apply, expandingFrequencyLow_apply, expandingFrequencyHigh_apply]
  split_ifs <;> simp

theorem exists_torusOddCommutator_frequency_remainder (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (K : SchwartzMap (EuclideanSpace ℝ (Fin 12)) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L), 1 ≤ R →
      let q := schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K
      ∀ (M : ℝ) (hM : 0 ≤ M)
        (hQB : ∀ x : UnitAddTorus (Fin 12), ‖expandingUnitTorusFunction a (N + 1 : ℕ) L q x‖ ^ (2 * m) ≤ M)
        (f : FourierL2) (j : Fin (N + 1) → Fin 12),
      ‖expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j f -
        expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j
          (expandingFrequencyLow L R f)‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨C, hC, hc⟩ := exists_torusOddCommutator_high_bound a N ha ha1 hN m K
  refine ⟨C, hC, ?_⟩
  intro L R hL hR q M hM hQB f j
  have hh := hc L R hL hR M hM hQB (expandingFrequencyHigh L R f) j (by
    intro n hn
    rw [expandingFrequencyHigh_apply]
    split_ifs
    rfl)
  have he := congrArg (expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j)
    (expandingFrequency_split L R f)
  rw [map_add] at he
  rw [he, add_sub_cancel_left]
  exact hh.trans (mul_le_mul_of_nonneg_left (expandingFrequencyHigh_norm_le L R f)
    (div_nonneg hC (by linarith)))

end DefocusingNLS

end OAI
