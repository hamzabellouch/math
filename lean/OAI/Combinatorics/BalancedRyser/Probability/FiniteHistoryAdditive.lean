import OAI.Combinatorics.BalancedRyser.Probability.BoundedDrift
import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistory

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem stronglyMeasurable_prefix (n : ℕ) (f : Prefix S n → ℝ) :
    StronglyMeasurable[filtration n] (fun ω : Path S => f (frestrictLe n ω)) := by
  apply Measurable.stronglyMeasurable
  change Measurable[Filtration.piLE n] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable f).comp (comap_measurable _)

theorem stronglyMeasurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    StronglyMeasurable[filtration (n + 1)] (stepObservable n f) := by
  let g : Prefix S (n + 1) → ℝ := fun h =>
    f (fun i => h ⟨i.1, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.2; omega)⟩)
      (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  exact stronglyMeasurable_prefix (n + 1) g

def additiveTrack (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ)
    (t : ℕ) (ω : Path S) : ℝ :=
  x₀ + ∑ j ∈ Finset.range t, stepObservable j (f j) ω

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] theorem additiveTrack_zero (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (ω : Path S) :
    additiveTrack x₀ f 0 ω = x₀ := by simp [additiveTrack]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] theorem additiveTrack_increment (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) (ω : Path S) :
    additiveTrack x₀ f (t + 1) ω - additiveTrack x₀ f t ω =
      stepObservable t (f t) ω := by
  simp only [additiveTrack, Finset.sum_range_succ]
  ring

theorem stronglyMeasurable_additiveTrack (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) :
    StronglyMeasurable[filtration t] (additiveTrack x₀ f t) := by
  apply StronglyMeasurable.add stronglyMeasurable_const
  have hs := Finset.stronglyMeasurable_sum (Finset.range t) (fun j hj =>
    (stronglyMeasurable_stepObservable j (f j)).mono
      (filtration.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))))
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply]

theorem condExp_additiveTrack_increment (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) :
    (pathLaw step s₀)[fun ω => additiveTrack x₀ f (t + 1) ω -
      additiveTrack x₀ f t ω | filtration t] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step t (ω t) s).toReal * f t (frestrictLe t ω) s := by
  simpa only [additiveTrack_increment] using condExp_stepObservable step s₀ t (f t)

theorem additiveTrack_drift_nonnegative (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (T : ℕ)
    (hmean : ∀ t < T, ∀ h : Prefix S t,
      0 ≤ ∑ s, (step t (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f t h s) :
    ∀ t ≤ T, ∀ᵐ ω ∂pathLaw step s₀,
      0 ≤ ∑ j ∈ Finset.range t,
        (pathLaw step s₀)[fun ω => additiveTrack x₀ f (j + 1) ω -
          additiveTrack x₀ f j ω | filtration j] ω := by
  intro t ht
  have hall := ae_all_iff.2 (fun j => condExp_additiveTrack_increment step s₀ x₀ f j)
  filter_upwards [hall] with ω hω
  apply Finset.sum_nonneg
  intro j hj
  rw [hω j]
  exact hmean j (lt_of_lt_of_le (Finset.mem_range.mp hj) ht) (frestrictLe j ω)

theorem additiveTrack_lower_tail (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (T : ℕ) (L : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L)
    (hbound : ∀ j < T, ∀ h s, |f j h s| ≤ L)
    (hmean : ∀ j < T, ∀ h : Prefix S j,
      0 ≤ ∑ s, (step j (h ⟨j, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f j h s)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) :
    (pathLaw step s₀).real {ω | additiveTrack x₀ f t ω ≤ x₀ - u} ≤
      2 * Real.exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  have hc := boundedDriftConcentration_proof (pathLaw step s₀) filtration
    (additiveTrack x₀ f) T L hT hL
    (fun j _ => stronglyMeasurable_additiveTrack x₀ f j)
    (fun j hj => Filter.Eventually.of_forall (fun ω => by
      simpa only [additiveTrack_increment, stepObservable] using hbound j hj (frestrictLe j ω) (ω (j + 1))))
    u hu t ht
  refine le_trans ?_ hc
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [additiveTrack_drift_nonnegative step s₀ x₀ f T hmean t ht]
    with ω hω hbad
  change additiveTrack x₀ f t ω ≤ x₀ - u at hbad
  simp only [additiveTrack_zero]
  have hneg : u ≤ -(additiveTrack x₀ f t ω - x₀ -
      ∑ j ∈ Finset.range t, (pathLaw step s₀)[fun ω =>
        additiveTrack x₀ f (j + 1) ω - additiveTrack x₀ f j ω | filtration j] ω) := by
    linarith
  exact hneg.trans (neg_le_abs _)

end Balanced.FiniteHistory

end

end OAI
