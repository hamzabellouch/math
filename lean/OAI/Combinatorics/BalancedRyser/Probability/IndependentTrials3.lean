import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.CondVar
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem abs_integral_sub_integral_le [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} {c : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ c) :
    |(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ| ≤ c := by
  rw [← integral_sub hf hg]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ f ω - g ω)
      (C := c) (by simpa only [Real.norm_eq_abs] using hfg))

theorem abs_sub_integral_le_of_oscillation [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {c : ℝ} (hf : Integrable f μ) (x : Ω)
    (hosc : ∀ᵐ y ∂μ, |f x - f y| ≤ c) :
    |f x - ∫ y, f y ∂μ| ≤ c := by
  simpa only [integral_const, probReal_univ, one_smul] using
    (abs_integral_sub_integral_le (integrable_const (f x)) hf hosc)

theorem averaged_oscillation {A : Type*} [IsProbabilityMeasure μ]
    {f : A → Ω → ℝ} {c : ℝ} (hf : ∀ a, Integrable (f a) μ)
    (hosc : ∀ a b, ∀ᵐ ω ∂μ, |f a ω - f b ω| ≤ c) :
    ∀ a b, |(∫ ω, f a ω ∂μ) - ∫ ω, f b ω ∂μ| ≤ c := by
  intro a b
  exact abs_integral_sub_integral_le (hf a) (hf b) (hosc a b)

theorem conditional_second_moment_le {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ᵐ ω ∂μ, |Z ω| ≤ c) :
    ∀ᵐ ω ∂μ, μ[(fun x ↦ (Z x) ^ 2) | m] ω ≤ c ^ 2 := by
  apply condExp_le_nonneg_const (sq_nonneg c)
  filter_upwards [hZ] with ω hω
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Z ω)) hc).2 hω

theorem conditional_variance_eq_second_moment {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} (hzero : μ[Z | m] =ᵐ[μ] 0) :
    ProbabilityTheory.condVar m Z μ =ᵐ[μ] μ[(fun x ↦ (Z x) ^ 2) | m] := by
  apply condExp_congr_ae
  filter_upwards [hzero] with ω hω
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.zero_apply] at hω ⊢
  rw [hω, sub_zero]

theorem conditional_variance_le_of_centered_bound {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hzero : μ[Z | m] =ᵐ[μ] 0) (hZ : ∀ᵐ ω ∂μ, |Z ω| ≤ c) :
    ∀ᵐ ω ∂μ, ProbabilityTheory.condVar m Z μ ω ≤ c ^ 2 := by
  filter_upwards [conditional_variance_eq_second_moment hzero,
    conditional_second_moment_le (m := m) hc hZ] with ω heq hle
  exact heq.trans_le hle

theorem martingale_increment_condExp_zero [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {D : ℕ → Ω → ℝ}
    (hD : Martingale D ℱ μ) (n : ℕ) :
    μ[(fun ω ↦ D (n + 1) ω - D n ω) | ℱ n] =ᵐ[μ] 0 := by
  filter_upwards [condExp_sub (hD.integrable (n + 1)) (hD.integrable n) (ℱ n),
    hD.condExp_ae_eq (Nat.le_succ n)] with ω hsub hnext
  change μ[D (n + 1) - D n | ℱ n] ω = 0
  rw [hsub]
  change μ[D (n + 1) | ℱ n] ω - μ[D n | ℱ n] ω = 0
  rw [hnext, condExp_of_stronglyMeasurable (ℱ.le n)
    (hD.stronglyMeasurable n) (hD.integrable n), sub_self]

theorem martingale_increment_condVar_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {D : ℕ → Ω → ℝ}
    (hD : Martingale D ℱ μ) (n : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |D (n + 1) ω - D n ω| ≤ c) :
    ∀ᵐ ω ∂μ, ProbabilityTheory.condVar (ℱ n)
      (fun x ↦ D (n + 1) x - D n x) μ ω ≤ c ^ 2 := by
  exact conditional_variance_le_of_centered_bound hc
    (martingale_increment_condExp_zero hD n) hbound

section RevealEndpoints

variable {T : ℕ} {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i))

@[simp] theorem prefixIndices_zero : prefixIndices T 0 = ∅ := by
  simp [prefixIndices]

@[simp] theorem prefixIndices_full : prefixIndices T T = Finset.univ := by
  ext i
  simp [prefixIndices]

@[simp] theorem prefixFiltration_zero : prefixFiltration ξ hξ 0 = ⊥ := by
  change (Filtration.piFinset (X := A) (prefixIndices T 0)).comap (trialVector ξ) = ⊥
  rw [prefixIndices_zero]
  have hempty : Filtration.piFinset (X := A) ∅ = ⊥ := by
    change MeasurableSpace.comap (Finset.restrict (∅ : Finset (Fin T))) _ = ⊥
    have hconst : Finset.restrict (∅ : Finset (Fin T)) =
        (fun _ : (i : Fin T) → A i ↦ fun i : (∅ : Finset (Fin T)) ↦
          False.elim (Finset.notMem_empty i.val i.property)) := by
      funext x i
      exact False.elim (Finset.notMem_empty i.val i.property)
    rw [hconst, MeasurableSpace.comap_const]
  rw [hempty, MeasurableSpace.comap_bot]

theorem piFinset_univ : Filtration.piFinset (X := A) Finset.univ =
    (inferInstance : MeasurableSpace ((i : Fin T) → A i)) := by
  apply le_antisymm (Filtration.piFinset.le _)
  have hid : @Measurable ((i : Fin T) → A i) ((i : Fin T) → A i)
      (Filtration.piFinset (X := A) Finset.univ) inferInstance id := by
    refine @Measurable.of_eval _ _ A
      (Filtration.piFinset (X := A) Finset.univ) _ id ?_
    intro i
    exact (measurable_pi_apply (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset (Fin T)))).comp
      (comap_measurable (Finset.restrict (Finset.univ : Finset (Fin T))))
  simpa only [MeasurableSpace.comap_id] using hid.comap_le

@[simp] theorem prefixFiltration_full : prefixFiltration ξ hξ T =
    MeasurableSpace.comap (trialVector ξ) inferInstance := by
  change (Filtration.piFinset (X := A) (prefixIndices T T)).comap (trialVector ξ) = _
  rw [prefixIndices_full, piFinset_univ]

theorem measurable_outcome_full {F : ((i : Fin T) → A i) → ℝ}
    (hF : Measurable F) :
    Measurable[prefixFiltration ξ hξ T] (fun ω ↦ F (trialVector ξ ω)) := by
  rw [prefixFiltration_full]
  exact hF.comp (comap_measurable (trialVector ξ))

theorem doobProcess_full [IsProbabilityMeasure μ]
    {F : ((i : Fin T) → A i) → ℝ} (hF : Measurable F)
    (hY : Integrable (fun ω ↦ F (trialVector ξ ω)) μ) :
    doobProcess ξ hξ (fun ω ↦ F (trialVector ξ ω)) μ T =
      fun ω ↦ F (trialVector ξ ω) := by
  exact condExp_of_stronglyMeasurable ((prefixFiltration ξ hξ).le T)
    (measurable_outcome_full ξ hξ hF).stronglyMeasurable hY

theorem doobProcess_zero [IsProbabilityMeasure μ] (Y : Ω → ℝ) :
    doobProcess ξ hξ Y μ 0 = fun _ ↦ ∫ ω, Y ω ∂μ := by
  rw [doobProcess, prefixFiltration_zero, condExp_bot]

omit [∀ i, MeasurableSpace (A i)] in
theorem CoordinateOscillation.abs_sub_le_sum
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (x y : (i : Fin T) → A i) :
    |F x - F y| ≤ ∑ i, c i := by
  classical
  let mix (s : Finset (Fin T)) : (i : Fin T) → A i :=
    fun i ↦ if i ∈ s then y i else x i
  have hmix (s : Finset (Fin T)) : |F (mix s) - F x| ≤ ∑ i ∈ s, c i := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert a s ha ih =>
      have hstep : |F (mix (insert a s)) - F (mix s)| ≤ c a := by
        apply hF a
        intro j hja
        simp [mix, hja]
      calc
        |F (mix (insert a s)) - F x| ≤
            |F (mix (insert a s)) - F (mix s)| + |F (mix s) - F x| :=
          abs_sub_le _ _ _
        _ ≤ c a + ∑ i ∈ s, c i := add_le_add hstep ih
        _ = ∑ i ∈ insert a s, c i := (Finset.sum_insert ha).symm
  have h := hmix Finset.univ
  simpa [mix, abs_sub_comm] using h

omit [∀ i, MeasurableSpace (A i)] in
theorem CoordinateOscillation.abs_le
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (x₀ x : (i : Fin T) → A i) :
    |F x| ≤ |F x₀| + ∑ i, c i := by
  calc
    |F x| = |F x - F x₀ + F x₀| := by rw [sub_add_cancel]
    _ ≤ |F x - F x₀| + |F x₀| := abs_add_le _ _
    _ ≤ (∑ i, c i) + |F x₀| := add_le_add (hF.abs_sub_le_sum x x₀) le_rfl
    _ = |F x₀| + ∑ i, c i := add_comm _ _

theorem CoordinateOscillation.integrable_comp [IsFiniteMeasure μ]
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (hFm : Measurable F)
    (x₀ : (i : Fin T) → A i) {g : Ω → (i : Fin T) → A i}
    (hg : Measurable g) : Integrable (fun ω ↦ F (g ω)) μ := by
  apply Integrable.of_bound (hFm.comp hg).aestronglyMeasurable (|F x₀| + ∑ i, c i)
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, Function.comp_apply] using hF.abs_le x₀ (g ω)

end RevealEndpoints

end Balanced.IndependentTrials

end

end OAI
