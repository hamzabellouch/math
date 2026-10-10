import OAI.NumberTheory.Ostmann.Arithmetic.MovingPivotDerivative

namespace OAI

/-! # Logarithmic derivatives of the actual terminal moving moduli -/

namespace Ostmann

noncomputable def MovingSlotData.realLeafModuli {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → TreeLeafIndex n → ℝ
  | _, .leaf _ regular, L, R, _ => L * R * MovingSlotReversal.naturalProduct value regular
  | _, .node s CL CR u left right, L, R, i =>
      let p := (MovingSlotData.step s CL CR u left right false).realPivot value L R
      match i with
      | .inl i => left.realLeafModuli value p L i
      | .inr i => right.realLeafModuli value p R i

/-- The quantitative cancellation test at every actual internal node. -/
def MovingSlotData.PivotControl {σ : Type*} (value : σ → ℕ) (A : ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR u left right, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let p := step.realPivot value L R
      0 < p ∧
        |(left.frequency : ℝ) * (MovingSlotReversal.naturalProduct value CR : ℝ) * R| +
          |(right.frequency : ℝ) * (MovingSlotReversal.naturalProduct value CL : ℝ) * L| ≤
          A * |(s : ℝ) * (MovingSlotReversal.naturalProduct value u : ℝ)| * p ∧
        left.PivotControl value A p L ∧ right.PivotControl value A p R

theorem positive_product_relative_derivative (X Y C dX dY D : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (hDX : |dX| ≤ D * X) (hDY : |dY| ≤ D * Y) :
    |(dX * Y + X * dY) * C| ≤ 2 * D * (X * Y * C) := by
  rw [abs_mul, abs_of_nonneg hC]
  calc
    _ ≤ (|dX * Y| + |X * dY|) * C :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) hC
    _ = (|dX| * Y + X * |dY|) * C := by
      rw [abs_mul, abs_mul, abs_of_nonneg hX, abs_of_nonneg hY]
    _ ≤ (D * X * Y + X * (D * Y)) * C := by gcongr
    _ = _ := by ring

/-- Each leaf modulus has logarithmic derivative at most `2*A^depth*D`.
The depth, rather than the number of leaves, controls the amplification. -/
theorem MovingSlotData.realLeafModuli_derivative {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (A D : ℝ) (hA : 1 ≤ A) (hD : 0 ≤ D)
    {L R : ℝ → ℝ} {x dL dR : ℝ} (hL : HasDerivAt L dL x) (hR : HasDerivAt R dR x)
    (hL0 : 0 < L x) (hR0 : 0 < R x) (hdL : |dL| ≤ D * L x) (hdR : |dR| ≤ D * R x)
    (hcontrol : T.PivotControl value A (L x) (R x)) (i : TreeLeafIndex n) :
    ∃ dM : ℝ,
      HasDerivAt (fun z => T.realLeafModuli value (L z) (R z) i) dM x ∧
      0 < T.realLeafModuli value (L x) (R x) i ∧
      |dM| ≤ 2 * A ^ n * D * T.realLeafModuli value (L x) (R x) i := by
  induction T generalizing D L R dL dR with
  | leaf s regular =>
    let C : ℝ := MovingSlotReversal.naturalProduct value regular
    have hC : 0 < C := by
      dsimp only [C]
      exact_mod_cast Nat.pos_of_ne_zero (MovingSlotReversal.naturalProduct_ne_zero value hvalue regular)
    refine ⟨(dL * R x + L x * dR) * C, (hL.mul hR).mul_const C, ?_, ?_⟩
    · change 0 < L x * R x * C
      positivity
    · simpa only [realLeafModuli, pow_zero, mul_one, mul_assoc] using
        positive_product_relative_derivative (L x) (R x) C dL dR D hL0.le hR0.le hC.le hdL hdR
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let P : ℝ → ℝ := fun z => step.realPivot value (L z) (R z)
    let dP := step.realPivot value dL dR
    have hp : HasDerivAt P dP x := step.realPivot_hasDerivAt value hL hR
    have hp0 : 0 < P x := hcontrol.1
    have hdP : |dP| ≤ (A * D) * P x :=
      moving_pivot_relative_derivative _ _ _ (L x) (R x) dL dR (P x) A D
        (mul_ne_zero (Int.cast_ne_zero.mpr hf.1)
          (Nat.cast_ne_zero.mpr (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)))
        hL0.le hR0.le hD hdL hdR hcontrol.2.1
    have hAD : 0 ≤ A * D := mul_nonneg (by linarith) hD
    have hDAD : D ≤ A * D := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hD
    have hdL' : |dL| ≤ (A * D) * L x := hdL.trans (mul_le_mul_of_nonneg_right hDAD hL0.le)
    have hdR' : |dR| ≤ (A * D) * R x := hdR.trans (mul_le_mul_of_nonneg_right hDAD hR0.le)
    cases i with
    | inl i =>
      obtain ⟨dM, hM, hM0, hdM⟩ := ihL hf.2.1 (A * D) hAD hp hL hp0 hL0 hdP hdL' hcontrol.2.2.1 i
      refine ⟨dM, hM, hM0, ?_⟩
      change |dM| ≤ 2 * A ^ (n + 1) * D * left.realLeafModuli value (P x) (L x) i
      convert hdM using 1; ring
    | inr i =>
      obtain ⟨dM, hM, hM0, hdM⟩ := ihR hf.2.2 (A * D) hAD hp hR hp0 hR0 hdP hdR' hcontrol.2.2.2 i
      refine ⟨dM, hM, hM0, ?_⟩
      change |dM| ≤ 2 * A ^ (n + 1) * D * right.realLeafModuli value (P x) (R x) i
      convert hdM using 1; ring

/-- In logarithmic coordinates the derivative bound no longer contains the
large leaf modulus. This is the quantity needed for smooth cutoffs. -/
theorem MovingSlotData.log_realLeafModuli_derivative {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (A D : ℝ) (hA : 1 ≤ A) (hD : 0 ≤ D)
    {L R : ℝ → ℝ} {x dL dR : ℝ} (hL : HasDerivAt L dL x) (hR : HasDerivAt R dR x)
    (hL0 : 0 < L x) (hR0 : 0 < R x) (hdL : |dL| ≤ D * L x) (hdR : |dR| ≤ D * R x)
    (hcontrol : T.PivotControl value A (L x) (R x)) (i : TreeLeafIndex n) :
    ∃ d : ℝ, HasDerivAt (fun z => Real.log (T.realLeafModuli value (L z) (R z) i)) d x ∧
      |d| ≤ 2 * A ^ n * D := by
  obtain ⟨dM, hM, hM0, hdM⟩ := T.realLeafModuli_derivative value hvalue hf A D hA hD
    hL hR hL0 hR0 hdL hdR hcontrol i
  refine ⟨_, hM.log (ne_of_gt hM0), ?_⟩
  rw [abs_div, abs_of_pos hM0]
  exact (div_le_iff₀ hM0).mpr hdM

end Ostmann

end OAI
