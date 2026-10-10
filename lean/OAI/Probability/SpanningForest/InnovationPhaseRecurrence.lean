import OAI.Probability.SpanningForest.InnovationSubdivision

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem336.InnovationPhaseRecurrence

def phaseOn {Ω : Type*} (A : Set Ω) (X Y : Ω → ℝ) : Ω → ℂ :=
  A.indicator (fun ω => Complex.exp (((Y ω - X ω : ℝ) : ℂ) * Complex.I))

lemma norm_phaseOn_le_one {Ω : Type*} (A : Set Ω) (X Y : Ω → ℝ) (ω : Ω) :
    ‖phaseOn A X Y ω‖ ≤ 1 := by
  classical
  by_cases hω : ω ∈ A
  · simp only [phaseOn, Set.indicator_of_mem hω, Complex.norm_exp_ofReal_mul_I]
    exact le_rfl
  · simp [phaseOn, hω]

lemma measurable_phaseOn {Ω : Type*} [MeasurableSpace Ω] {A : Set Ω} {X Y : Ω → ℝ}
    (hA : MeasurableSet A) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (phaseOn A X Y) := by
  apply Measurable.indicator _ hA
  fun_prop

lemma phaseOn_mul_increment {Ω : Type*} (A : Set Ω) (X Y Z : Ω → ℝ) (ω : Ω) :
    phaseOn A X Y ω * Complex.exp (((Z ω - Y ω : ℝ) : ℂ) * Complex.I) =
      phaseOn A X Z ω := by
  classical
  by_cases hω : ω ∈ A
  · simp only [phaseOn, Set.indicator_of_mem hω]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [phaseOn, hω]

lemma integral_phaseOn_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} (hA : MeasurableSet A) (X : Ω → ℝ) :
    (∫ ω, phaseOn A X X ω ∂P) = (P.real A : ℂ) := by
  simp [phaseOn, integral_indicator hA]

lemma integral_phaseOn_eq_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} (hA : MeasurableSet A) (X Y : Ω → ℝ) :
    (∫ ω, phaseOn A X Y ω ∂P) =
      ∫ ω in A, Complex.exp (((Y ω - X ω : ℝ) : ℂ) * Complex.I) ∂P := by
  exact integral_indicator hA

lemma phase_recurrence_of_weighted_step {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : Set Ω) (X Y Z : Ω → ℝ) (a : ℂ) (ε : ℝ)
    (hstep : ‖(∫ ω, phaseOn A X Y ω *
        Complex.exp (((Z ω - Y ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (∫ ω, phaseOn A X Y ω ∂P) * a‖ ≤ ε) :
    ‖(∫ ω, phaseOn A X Z ω ∂P) - a * (∫ ω, phaseOn A X Y ω ∂P)‖ ≤ ε := by
  simp only [phaseOn_mul_increment] at hstep
  simpa only [mul_comm] using hstep

theorem restricted_characteristic_of_phase_steps
    {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    {A : Set Ω} (hA : MeasurableSet A)
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (C duration v : ℝ) (hduration : 0 ≤ duration) (hv : 0 ≤ v)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖(∫ ω, phaseOn A (X s) (X (τ n k)) ω *
          Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, phaseOn A (X s) (X (τ n k)) ω ∂P) *
            (Real.exp (-(duration / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)‖ ≤
        C * (duration / ((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (duration / ((n + 1 : ℕ) : ℝ))) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * v) : ℂ) * (P.real A : ℂ) := by
  let μ : ℕ → ℕ → ℂ := fun n k => ∫ ω, phaseOn A (X s) (X (τ n k)) ω ∂P
  apply InnovationSubdivision.gaussian_identity_of_subdivision_recurrences
    _ _ μ C duration v hduration hv
  · intro n
    dsimp [μ]
    rw [hstart n]
    exact integral_phaseOn_self hA (X s)
  · intro n
    dsimp [μ]
    rw [hfinish n]
    exact integral_phaseOn_eq_setIntegral hA (X s) (X t)
  · filter_upwards [hstep] with n hn
    intro k hk
    exact phase_recurrence_of_weighted_step A (X s) (X (τ n k))
      (X (τ n (k + 1))) _ _ (hn k hk)

theorem restricted_characteristic_of_bounded_test_steps
    {Ω T : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    (past : ℕ → ℕ → MeasurableSpace Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    (hApast : ∀ n k, MeasurableSet[past n k] A)
    (hXstart : ∀ n k, Measurable[past n k] (X s))
    (hXpast : ∀ n k, Measurable[past n k] (X (τ n k)))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (C duration v : ℝ) (hduration : 0 ≤ duration) (hv : 0 ≤ v)
    (hlocal : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1, ∀ K : Ω → ℂ,
      Measurable[past n k] K → (∀ ω, ‖K ω‖ ≤ 1) →
      ‖(∫ ω, K ω *
          Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, K ω ∂P) * (Real.exp (-(duration / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)‖ ≤
        C * (duration / ((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (duration / ((n + 1 : ℕ) : ℝ))) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * v) : ℂ) * (P.real A : ℂ) := by
  apply restricted_characteristic_of_phase_steps X s t τ hA hstart hfinish
    C duration v hduration hv
  filter_upwards [hlocal] with n hn
  intro k hk
  exact hn k hk (phaseOn A (X s) (X (τ n k)))
    (@measurable_phaseOn Ω (past n k) A (X s) (X (τ n k))
      (hApast n k) (hXstart n k) (hXpast n k))
    (norm_phaseOn_le_one A (X s) (X (τ n k)))

theorem restricted_characteristic_of_adapted_bounded_test_steps
    {Ω T : Type*} [mΩ : MeasurableSpace Ω] [Preorder T] {P : Measure Ω}
    (ℱ : Filtration T mΩ) (X : T → Ω → ℝ) (hX : Adapted ℱ X)
    (s t : T) (τ : ℕ → ℕ → T)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hle : ∀ n k, s ≤ τ n k)
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (C duration v : ℝ) (hduration : 0 ≤ duration) (hv : 0 ≤ v)
    (hlocal : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1, ∀ K : Ω → ℂ,
      Measurable[ℱ (τ n k)] K → (∀ ω, ‖K ω‖ ≤ 1) →
      ‖(∫ ω, K ω *
          Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, K ω ∂P) * (Real.exp (-(duration / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)‖ ≤
        C * (duration / ((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (duration / ((n + 1 : ℕ) : ℝ))) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * v) : ℂ) * (P.real A : ℂ) := by
  apply restricted_characteristic_of_bounded_test_steps X s t τ
    (fun n k => ℱ (τ n k)) (ℱ.le s A hA)
    (fun n k => ℱ.mono (hle n k) A hA)
    (fun n k => (hX s).mono (ℱ.mono (hle n k)) le_rfl)
    (fun n k => hX (τ n k)) hstart hfinish C duration v hduration hv hlocal

def timeGrid (s d : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  s + (k : ℝ≥0) * (d / ((n + 1 : ℕ) : ℝ≥0))

@[simp] lemma timeGrid_zero (s d : ℝ≥0) (n : ℕ) : timeGrid s d n 0 = s := by
  simp [timeGrid]

@[simp] lemma timeGrid_finish (s d : ℝ≥0) (n : ℕ) :
    timeGrid s d n (n + 1) = s + d := by
  simp [timeGrid, mul_div_cancel₀]

lemma timeGrid_mono (s d : ℝ≥0) (n : ℕ) : Monotone (timeGrid s d n) := by
  intro k l hkl
  dsimp [timeGrid]
  gcongr

lemma le_timeGrid (s d : ℝ≥0) (n k : ℕ) : s ≤ timeGrid s d n k := by
  exact le_add_of_nonneg_right zero_le

lemma timeGrid_le_finish (s d : ℝ≥0) (n k : ℕ) (hk : k ≤ n + 1) :
    timeGrid s d n k ≤ s + d := by
  simpa only [timeGrid_finish] using timeGrid_mono s d n hk

lemma timeGrid_succ_sub (s d : ℝ≥0) (n k : ℕ) :
    (timeGrid s d n (k + 1) : ℝ) - (timeGrid s d n k : ℝ) =
      (d : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  simp only [timeGrid, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
  ring

theorem restricted_characteristic_of_local_bounded_test_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (hX : Adapted ℱ X)
    (s d : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (C rate δ : ℝ) (hrate : 0 ≤ rate) (hδ : 0 < δ)
    (hlocal : ∀ u v : ℝ≥0, s ≤ u → u ≤ v → v ≤ s + d →
      (v : ℝ) - (u : ℝ) ≤ δ → ∀ K : Ω → ℂ,
      Measurable[ℱ u] K → (∀ ω, ‖K ω‖ ≤ 1) →
      ‖(∫ ω, K ω *
          Complex.exp (((X v ω - X u ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, K ω ∂P) * (Real.exp (-((v : ℝ) - (u : ℝ)) * rate) : ℂ)‖ ≤
        C * ((v : ℝ) - (u : ℝ)) * Real.sqrt ((v : ℝ) - (u : ℝ))) :
    (∫ ω in A, Complex.exp (((X (s + d) ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-(d : ℝ) * rate) : ℂ) * (P.real A : ℂ) := by
  apply restricted_characteristic_of_adapted_bounded_test_steps ℱ X hX s (s + d)
    (timeGrid s d) hA (le_timeGrid s d) (timeGrid_zero s d) (timeGrid_finish s d)
    C (d : ℝ) rate d.property hrate
  have hlim : Tendsto (fun n : ℕ => (d : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  intro k hk K hK hKbound
  have hb := hlocal (timeGrid s d n k) (timeGrid s d n (k + 1))
    (le_timeGrid s d n k) (timeGrid_mono s d n (Nat.le_succ k))
    (timeGrid_le_finish s d n (k + 1) (Nat.succ_le_of_lt hk))
    (by rw [timeGrid_succ_sub]; exact hn.le) K hK hKbound
  simpa only [timeGrid_succ_sub] using hb

end Problem336.InnovationPhaseRecurrence

end

end OAI
