import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionKernel

namespace OAI

noncomputable section
open scoped BigOperators
open Filter
open scoped Topology

namespace Balanced.SelectedDeletion.SuccessAudit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem initial_probability_nonneg (c C : ℝ) :
    0 ≤ offsetEventProbability {M : MergedPairs F | InitialGood M c C} := by
  rw [offsetEventProbability_eq_sum]
  exact Finset.sum_nonneg fun M _ => by split_ifs <;> positivity

theorem initial_probability_le_one (c C : ℝ) :
    offsetEventProbability {M : MergedPairs F | InitialGood M c C} ≤ 1 := by
  rw [offsetEventProbability_eq_sum, ← offset_sum_real (F := F)]
  apply Finset.sum_le_sum
  intro M _
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem success_le_initial (κ : Kernel F) {c C : ℝ}
    (hκ : IsExperiment κ c C) :
    successMass κ ≤
      offsetEventProbability {M : MergedPairs F | InitialGood M c C} := by
  classical
  rw [offsetEventProbability_eq_sum]
  simp only [successMass, jointMass]
  apply Finset.sum_le_sum
  intro M _
  by_cases hM : InitialGood M c C
  · simp only [ite_eq_left hM]
    have hw : 0 ≤ ((offsetLaw F) M).toReal := ENNReal.toReal_nonneg
    have hm := mul_le_mul_of_nonneg_left (hκ.2.1 M) hw
    simpa using hm
  · simp [hM, hκ.2.2.1 M hM]

theorem initial_mul_one_sub_error_le_success (κ : Kernel F) {c C ε : ℝ}
    (hκ : IsExperiment κ c C)
    (hfixed : ∀ M, InitialGood M c C → 1 - ε ≤ fixedSuccessMass κ M) :
    (1 - ε) * offsetEventProbability {M : MergedPairs F | InitialGood M c C} ≤
      successMass κ := by
  classical
  rw [offsetEventProbability_eq_sum]
  simp only [successMass, jointMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M _
  by_cases hM : InitialGood M c C
  · simp only [ite_eq_left hM]
    simpa [fixedSuccessMass, Finset.mul_sum, mul_comm] using
      mul_le_mul_of_nonneg_left (hfixed M hM)
        (ENNReal.toReal_nonneg : 0 ≤ ((offsetLaw F) M).toReal)
  · simp [hM, hκ.2.2.1 M hM]

theorem abs_success_sub_initial_le (κ : Kernel F) {c C ε : ℝ}
    (hκ : IsExperiment κ c C) (hε : 0 ≤ ε)
    (hfixed : ∀ M, InitialGood M c C → 1 - ε ≤ fixedSuccessMass κ M) :
    |successMass κ -
      offsetEventProbability {M : MergedPairs F | InitialGood M c C}| ≤ ε := by
  have hu := success_le_initial κ hκ
  have hl := initial_mul_one_sub_error_le_success κ hκ hfixed
  have hp := initial_probability_le_one (F := F) c C
  have he := mul_le_mul_of_nonneg_left hp hε
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith

section VaryingFields

variable {ι : Type*} {l : Filter ι} {Fs : ι → Type*}
  [∀ i, Field (Fs i)] [∀ i, Fintype (Fs i)] [∀ i, DecidableEq (Fs i)]

theorem tendsto_success_of_tendsto_initial
    (κ : ∀ i, Kernel (Fs i)) {c C p : ℝ} (ε : ι → ℝ)
    (hκ : ∀ᶠ i in l, IsExperiment (κ i) c C)
    (hfixed : ∀ᶠ i in l, ∀ M, InitialGood M c C →
      1 - ε i ≤ fixedSuccessMass (κ i) M)
    (hε : Tendsto ε l (𝓝 0))
    (hpass : Tendsto (fun i => offsetEventProbability
      {M : MergedPairs (Fs i) | InitialGood M c C}) l (𝓝 p)) :
    Tendsto (fun i => successMass (κ i)) l (𝓝 p) := by
  have hl : Tendsto (fun i => (1 - ε i) * offsetEventProbability
      {M : MergedPairs (Fs i) | InitialGood M c C}) l (𝓝 p) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).mul hpass
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hpass
  · filter_upwards [hκ, hfixed] with i hi hfi
    exact initial_mul_one_sub_error_le_success (κ i) hi hfi
  · filter_upwards [hκ] with i hi
    exact success_le_initial (κ i) hi

theorem tendsto_success_exp_neg_one
    (κ : ∀ i, Kernel (Fs i)) {c C : ℝ} (ε : ℕ → ℝ)
    (hκ : ∀ᶠ i in l, IsExperiment (κ i) c C)
    (hfixed : ∀ᶠ i in l, ∀ M, InitialGood M c C →
      1 - ε (Fintype.card (Fs i)) ≤ fixedSuccessMass (κ i) M)
    (hε : Tendsto ε atTop (𝓝 0))
    (hq : Tendsto (fun i => Fintype.card (Fs i)) l atTop)
    (hpass : Tendsto (fun i => offsetEventProbability
      {M : MergedPairs (Fs i) | InitialGood M c C}) l (𝓝 (Real.exp (-1)))) :
    Tendsto (fun i => successMass (κ i)) l (𝓝 (Real.exp (-1))) :=
  tendsto_success_of_tendsto_initial κ (fun i => ε (Fintype.card (Fs i)))
    hκ hfixed (hε.comp hq) hpass

end VaryingFields

end Balanced.SelectedDeletion.SuccessAudit

end

end OAI
