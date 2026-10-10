import OAI.NumberTheory.JointDickman.Probability.FiniteChannels

namespace OAI

/-!
# The finite low-exclusive kernel

The common variable and the two exclusive variables have independent
finite masses. Cells are specified by an `Option`-valued map, allowing
discarded outputs. Restricting the second exclusive variable to `low`
has separate row and column estimates, proved from these actual masses.
-/

namespace JointDickman

open scoped BigOperators

section

variable {C E A : Type*} [Fintype C] [Fintype E] [Fintype A] [DecidableEq A]

noncomputable def optionCellMass (v : E → ℝ) (cell : E → Option A) (a : A) : ℝ :=
  ∑ e, if cell e = some a then v e else 0

omit [Fintype A] in
theorem optionCellMass_nonneg (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) (a : A) : 0 ≤ optionCellMass v cell a := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> [exact hv e; exact le_rfl]

theorem optionCellMass_sum_le (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) : (∑ a, optionCellMass v cell a) ≤ ∑ e, v e := by
  unfold optionCellMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  cases h : cell e with
  | none => simpa [h] using hv e
  | some a => simp

noncomputable def lowExclusiveProbability (v : E → ℝ) (low : E → Prop)
    [DecidablePred low] : ℝ := ∑ e, if low e then v e else 0

theorem lowExclusiveProbability_nonneg (v : E → ℝ) (low : E → Prop)
    [DecidablePred low] (hv : ∀ e, 0 ≤ v e) : 0 ≤ lowExclusiveProbability v low := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> [exact hv e; exact le_rfl]

noncomputable def independentCellMarginal (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a

/-- The common mass is integrated after multiplying the two independent
exclusive cell probabilities; only the second exclusive is restricted. -/
noncomputable def lowExclusiveMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a *
    optionCellMass (fun e => if low e then v e else 0) (cell c) b

omit [Fintype A] in
theorem lowExclusiveMass_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a b : A) :
    0 ≤ lowExclusiveMass w v cell low a b := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (mul_nonneg (hw c) (optionCellMass_nonneg v (cell c) hv a))
    (optionCellMass_nonneg _ (cell c) (fun e => by split_ifs <;> [exact hv e; exact le_rfl]) b)

omit [Fintype A] in
/-- This factorized definition is precisely the restricted independent
triple law; it includes no assumption about its row or column behavior. -/
theorem lowExclusiveMass_eq_triple (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) :
    lowExclusiveMass w v cell low a b =
      ∑ c, ∑ e₂, ∑ e₁, if low e₂ ∧ cell c e₁ = some a ∧ cell c e₂ = some b then
        w c * v e₁ * v e₂ else 0 := by
  unfold lowExclusiveMass optionCellMass
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e₂ _
  apply Finset.sum_congr rfl
  intro e₁ _
  by_cases hlow : low e₂ <;> by_cases ha : cell c e₁ = some a <;>
    by_cases hb : cell c e₂ = some b <;> simp [hlow, ha, hb]

/-- The row estimate uses the fact that an exclusive output belongs to
at most one retained cell. -/
theorem lowExclusiveMass_row (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a : A) :
    (∑ b, lowExclusiveMass w v cell low a b) ≤
      lowExclusiveProbability v low * independentCellMarginal w v cell a := by
  have hlow : ∀ e, 0 ≤ if low e then v e else 0 := by
    intro e
    split_ifs <;> [exact hv e; exact le_rfl]
  calc
    _ = ∑ c, (w c * optionCellMass v (cell c) a) *
        (∑ b, optionCellMass (fun e => if low e then v e else 0) (cell c) b) := by
      unfold lowExclusiveMass
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ c, (w c * optionCellMass v (cell c) a) * lowExclusiveProbability v low := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (optionCellMass_sum_le _ (cell c) hlow)
        (mul_nonneg (hw c) (optionCellMass_nonneg v (cell c) hv a))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

omit [Fintype A] in
/-- Integrating the common variable after conditioning on the restricted
exclusive variable. This is the precise conditional mass used for columns. -/
theorem lowExclusiveMass_integrate_common (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (b : A) :
    (∑ c, w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b) =
      ∑ e, if low e then v e * optionCellMass w (fun c => cell c e) b else 0 := by
  unfold optionCellMass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : low e
  · simp only [hl, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : cell c e = some b <;> simp [hc, mul_comm]
  · simp [hl]

/-- The column estimate uses the normalized first exclusive law and a
uniform conditional common-variable cell estimate at every low exclusive. -/
theorem lowExclusiveMass_column (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {H : ℝ} (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H)
    (b : A) : (∑ a, lowExclusiveMass w v cell low a b) ≤ lowExclusiveProbability v low * H := by
  have hlow : ∀ e, 0 ≤ if low e then v e else 0 := by
    intro e
    split_ifs <;> [exact hv e; exact le_rfl]
  calc
    _ = ∑ c, (w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b) *
        (∑ a, optionCellMass v (cell c) a) := by
      unfold lowExclusiveMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ c, w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b := by
      apply Finset.sum_le_sum
      intro c _
      have hsum := optionCellMass_sum_le v (cell c) hv
      rw [hv1] at hsum
      simpa using mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (hw c) (optionCellMass_nonneg _ (cell c) hlow b))
    _ = ∑ e, if low e then v e * optionCellMass w (fun c => cell c e) b else 0 :=
      lowExclusiveMass_integrate_common w v cell low b
    _ ≤ ∑ e, if low e then v e * H else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · exact mul_le_mul_of_nonneg_left (hcommon e he b) (hv e)
      · exact le_rfl
    _ = _ := by simp only [lowExclusiveProbability, Finset.sum_mul, ite_mul, zero_mul]

/-- Equal cell atom weights give the manuscript's `m⁻²` kernel. -/
noncomputable def lowExclusiveKernel (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (m : ℝ) (a b : A) : ℝ := lowExclusiveMass w v cell low a b / (m * m)

theorem lowExclusiveKernel_weighted_row (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) {m : ℝ} (hm : 0 < m) (a : A) :
    (∑ b, m * |lowExclusiveKernel w v cell low m a b|) ≤
      lowExclusiveProbability v low * independentCellMarginal w v cell a / m := by
  have he (b : A) : m * |lowExclusiveKernel w v cell low m a b| =
      lowExclusiveMass w v cell low a b / m := by
    unfold lowExclusiveKernel
    rw [abs_of_nonneg (div_nonneg (lowExclusiveMass_nonneg w v cell low hw hv a b)
      (mul_pos hm hm).le)]
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (lowExclusiveMass_row w v cell low hw hv a) hm.le

theorem lowExclusiveKernel_weighted_column (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {m H : ℝ} (hm : 0 < m)
    (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H) (b : A) :
    (∑ a, m * |lowExclusiveKernel w v cell low m a b|) ≤ lowExclusiveProbability v low * H / m := by
  have he (a : A) : m * |lowExclusiveKernel w v cell low m a b| =
      lowExclusiveMass w v cell low a b / m := by
    unfold lowExclusiveKernel
    rw [abs_of_nonneg (div_nonneg (lowExclusiveMass_nonneg w v cell low hw hv a b)
      (mul_pos hm hm).le)]
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (lowExclusiveMass_column w v cell low hw hv hv1 hcommon b) hm.le

/-- A finite Schur conclusion derived from the two distinct local-law
estimates; neither a discarded-event operator bound nor a row bound is assumed. -/
theorem lowExclusiveKernel_square_bound (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {m H : ℝ} (hm : 0 < m) (hH : 0 ≤ H)
    (hmarginal : ∀ a, independentCellMarginal w v cell a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H * m)
    (f : A → ℝ) :
    (∑ a, m * finiteKernelAction (fun _ => m) (lowExclusiveKernel w v cell low m) f a ^ 2) ≤
      (lowExclusiveProbability v low * H) ^ 2 * ∑ a, m * f a ^ 2 := by
  have hσ := lowExclusiveProbability_nonneg v low hv
  have hrow (a : A) : (∑ b, m * |lowExclusiveKernel w v cell low m a b|) ≤
      lowExclusiveProbability v low * H := by
    refine (lowExclusiveKernel_weighted_row w v cell low hw hv hm a).trans ?_
    calc
      _ ≤ lowExclusiveProbability v low * (H * m) / m :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hmarginal a) hσ) hm.le
      _ = _ := by field_simp
  have hcol (b : A) : (∑ a, m * |lowExclusiveKernel w v cell low m a b|) ≤
      lowExclusiveProbability v low * H := by
    have h := lowExclusiveKernel_weighted_column w v cell low hw hv hv1 hm hcommon b
    refine h.trans_eq ?_
    field_simp
  exact finiteKernelAction_square_bound (fun _ => m) _ (fun _ => hm.le)
    (mul_nonneg hσ hH) hrow hcol f

end

end JointDickman

end OAI
