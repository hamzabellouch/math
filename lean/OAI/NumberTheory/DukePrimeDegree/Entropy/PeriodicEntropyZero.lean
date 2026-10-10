import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalPeriodicity
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalFiberRecoding
import Mathlib.Dynamics.PeriodicPts.Defs

namespace OAI

/-! # Almost-everywhere periodicity gives zero finite-observation entropy

A common positive period makes every long orbit name a deterministic
extension of one fixed finite name.  Thus block entropy stays bounded and
its entropy rate is zero.  Combining this with full-A ergodicity isolates
the aperiodic branch without asserting ergodicity of the chosen map.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def periodicNameExtension (α : Type*) (n : ℕ) (hn : 0 < n) (N : ℕ)
    (w : Fin n → α) : Fin N → α :=
  fun j => w ⟨j.val % n, Nat.mod_lt _ hn⟩

lemma ae_orbitName_periodic_extension {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T : Y → Y) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) (P : Y → α) (N : ℕ) :
    orbitName T P N =ᵐ[μ] fun x => periodicNameExtension α n hn N (orbitName T P n x) := by
  filter_upwards [hperiod] with x hx
  funext j
  change P (T^[j.val] x) = P (T^[j.val % n] x)
  exact congrArg P ((show Function.IsPeriodicPt T n x from hx).iterate_mod_apply j.val).symm

/-- The bound is independent of the length of the observed orbit. -/
theorem orbitEntropy_le_period_name {Y α : Type*}
    [MeasurableSpace Y] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (T : Y → Y) (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (hperiod : ∀ᵐ x ∂μ, T^[n] x = x)
    (P : Y → α) (hP : Measurable P) (N : ℕ) :
    observationEntropy μ (orbitName T P N) ≤ observationEntropy μ (orbitName T P n) := by
  let Q := orbitName T P n
  have hQ : Measurable Q := measurable_pi_iff.mpr (fun j => hP.comp (hT.iterate j.val))
  rw [observationEntropy_eq_of_ae_eq μ _ _
    (ae_orbitName_periodic_extension μ T n hn hperiod P N)]
  apply observationEntropy_le_of_refines μ _ Q
    (fun w => ((measurable_of_finite (periodicNameExtension α n hn N)).comp hQ)
      (measurableSet_singleton w))
    (fun w => hQ (measurableSet_singleton w))
  intro x y hxy
  exact congrArg (periodicNameExtension α n hn N) hxy

theorem observationEntropyRate_zero_of_ae_periodic {Y α : Type*}
    [MeasurableSpace Y] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) (P : Y → α) (hP : Measurable P) :
    observationEntropyRate μ T P = 0 := by
  have hPf (a : α) : MeasurableSet {x | P x = a} := hP (measurableSet_singleton a)
  have hu : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N) / (N : ℝ) ≤
        observationEntropy μ (orbitName T P n) / (N : ℝ) :=
    Filter.Eventually.of_forall fun N => div_le_div_of_nonneg_right
      (orbitEntropy_le_period_name μ T hT.measurable n hn hperiod P hP N) (Nat.cast_nonneg N)
  have hz : Tendsto (fun N : ℕ => observationEntropy μ (orbitName T P n) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact le_antisymm
    (le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hPf) hz hu)
    (observationEntropyRate_nonneg μ hT.measurable P hPf)

theorem measureEntropy_zero_of_ae_periodic {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) : measureEntropy μ T = 0 := by
  apply le_antisymm
  · change (⨆ k : ℕ, ⨆ P : Y → Fin k,
      ⨆ (_hP : ∀ a, MeasurableSet {y | P y = a}),
        ENNReal.ofReal (observationEntropyRate μ T P)) ≤ (0 : ℝ≥0∞)
    simp only [iSup_le_iff]
    intro k P hP
    rw [observationEntropyRate_zero_of_ae_periodic μ hT n hn hperiod P
      (measurable_to_countable' hP), ENNReal.ofReal_zero]
  · exact bot_le

/-- Full diagonal ergodicity gives a zero-entropy/aperiodic dichotomy for
every fixed real-time diagonal map. -/
theorem diagonal_entropy_zero_or_aperiodic (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) = 0 ∨
    (∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n →
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x ≠ x) := by
  rcases diagonal_periodicity_dichotomy d ell hell t μ with ⟨n, hn, hp⟩ | hap
  · left
    have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell t)) μ μ := by
      refine ⟨(continuous_rightAction _).measurable, ?_⟩
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hA _
    exact measureEntropy_zero_of_ae_periodic μ hT n hn hp
  · exact Or.inr hap

theorem diagonal_aperiodic_of_positive_entropy (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hpos : 0 < measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t))) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n →
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x ≠ x := by
  rcases diagonal_entropy_zero_or_aperiodic d ell hell t μ with hz | hap
  · rw [hz] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hap

end DukePrimeDegree

end

end OAI
