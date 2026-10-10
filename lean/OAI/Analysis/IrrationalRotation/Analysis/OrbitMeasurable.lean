import OAI.Analysis.IrrationalRotation.Model.OrbitMeasurable
import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Analysis.ErgodicAtoms
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

open Set Filter Function MeasureTheory
open scoped ENNReal

namespace Invariant233

variable {X Y : Type*} [m : MeasurableSpace X] [mY : MeasurableSpace Y]

omit m in

theorem measurable_orbit_observable (σ : Equiv.Perm X) (f : X → Y) (n : ℤ) :
    @Measurable X Y (orbitMeasurableSpace σ f) mY (fun x => f ((σ ^ n) x)) :=
  Measurable.of_comap_le (le_iSup (fun n : ℤ =>
    MeasurableSpace.comap (fun x => f ((σ ^ n) x)) mY) n)

omit m in

theorem measurable_base_observable (σ : Equiv.Perm X) (f : X → Y) :
    @Measurable X Y (orbitMeasurableSpace σ f) mY f := by
  simpa using measurable_orbit_observable σ f 0

theorem measurable_perm_zpow (σ : Equiv.Perm X)
    (hσ : Measurable σ) (hinv : Measurable σ.symm) (n : ℤ) :
    Measurable (σ ^ n) := by
  cases n with
  | ofNat n => simpa [Equiv.Perm.coe_pow] using hσ.iterate n
  | negSucc n =>
      simpa [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using hinv.iterate (n + 1)

theorem orbitMeasurableSpace_le (σ : Equiv.Perm X) {f : X → Y}
    (hσ : Measurable σ) (hinv : Measurable σ.symm) (hf : Measurable f) :
    orbitMeasurableSpace σ f ≤ m := by
  apply iSup_le
  intro n
  exact (hf.comp (measurable_perm_zpow σ hσ hinv n)).comap_le

omit m in

theorem measurable_perm_zpow_orbit (σ : Equiv.Perm X) (f : X → Y) (k : ℤ) :
    @Measurable X X (orbitMeasurableSpace σ f) (orbitMeasurableSpace σ f) ((σ ^ k : Equiv.Perm X) : X → X) := by
  apply Measurable.of_comap_le
  unfold orbitMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro n
  rw [MeasurableSpace.comap_comp]
  have heq : (fun x => f ((σ ^ n) x)) ∘ (σ ^ k) =
      fun x => f ((σ ^ (n + k)) x) := by
    funext x
    simp only [comp_apply, zpow_add, Equiv.Perm.mul_apply]
  rw [heq]
  exact le_iSup (fun n : ℤ =>
    MeasurableSpace.comap (fun x => f ((σ ^ n) x)) mY) (n + k)

theorem exists_nontrivial_set_of_not_ae_constant
    [Nonempty Y] [MeasurableSpace.CountablySeparated Y]
    {μ : Measure X} (m₀ : MeasurableSpace X) {f : X → Y}
    (hf : @Measurable X Y m₀ mY f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c) :
    ∃ s : Set X, @MeasurableSet X m₀ s ∧ μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
  let : MeasurableSpace X := m
  by_contra hsets
  apply hnonconstant
  refine Filter.exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  have hpre : @MeasurableSet X m₀ (f ⁻¹' U) := hf hU
  by_cases hz : μ (f ⁻¹' U) = 0
  · right
    exact eventuallyEqSet_empty.mp (ae_eq_empty.mpr hz)
  · left
    have hc : μ (f ⁻¹' U)ᶜ = 0 := by
      by_contra hc
      exact hsets ⟨f ⁻¹' U, hpre, hz, hc⟩
    exact eventuallyEqSet_univ.mp (ae_eq_univ.mpr hc)

theorem orbitMeasurableSpace_atomless
    [Nonempty Y] [MeasurableSpace.CountablySeparated Y]
    {μ : Measure X} [IsFiniteMeasure μ]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c)
    {s : Set X} (hs : @MeasurableSet X (orbitMeasurableSpace σ f) s)
    (hpos : μ s ≠ 0) :
    ∃ t : Set X, @MeasurableSet X (orbitMeasurableSpace σ f) t ∧
      t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  apply ErgodicAtoms.exists_nontrivial_measurable_subset htotal
    (orbitMeasurableSpace σ f) (orbitMeasurableSpace_le σ hσ hinv hf) ?_ ?_ hs hpos
  · simpa using measurable_perm_zpow_orbit σ f 1
  · exact exists_nontrivial_set_of_not_ae_constant (orbitMeasurableSpace σ f)
      (measurable_base_observable σ f) hnonconstant

theorem not_ae_constant_of_infinite_log_cost
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) :
    ¬ ∃ c : ℝ, f =ᵐ[μ] Function.const X c := by
  rintro ⟨c, hc⟩
  have hcost : (fun x => ENNReal.ofReal (-Real.log (f x))) =ᵐ[μ]
      fun _ => ENNReal.ofReal (-Real.log c) := by
    filter_upwards [hc] with x hx
    simp only [hx, Function.const_apply]
  have hfinite : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) ≠ ∞ := by
    rw [lintegral_congr_ae hcost, lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ Set.univ)
  exact hfinite hlog

theorem not_ae_constant_of_negInfiniteLogIntegral
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hnonzero : ∀ᵐ x ∂μ, f x ≠ 0)
    (hlog : HasNegInfiniteLogIntegral μ f) :
    ¬ ∃ c : ℝ, f =ᵐ[μ] Function.const X c := by
  apply not_ae_constant_of_infinite_log_cost
  change (∫⁻ x, negLogCost (f x) ∂μ) = ∞ at hlog
  have hphase : (fun x => negLogCost (f x)) =ᵐ[μ]
      fun x => ENNReal.ofReal (-Real.log (f x)) := by
    filter_upwards [hnonzero] with x hx
    simp only [negLogCost, ite_eq_right hx, Real.log_abs]
  rwa [lintegral_congr_ae hphase] at hlog

theorem orbitMeasurableSpace_atomless_of_negInfiniteLogIntegral
    {μ : Measure X} [IsFiniteMeasure μ]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → ℝ} (hf : Measurable f)
    (hnonzero : ∀ᵐ x ∂μ, f x ≠ 0) (hlog : HasNegInfiniteLogIntegral μ f)
    {s : Set X} (hs : @MeasurableSet X (orbitMeasurableSpace σ f) s)
    (hpos : μ s ≠ 0) :
    ∃ t : Set X, @MeasurableSet X (orbitMeasurableSpace σ f) t ∧
      t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  exact orbitMeasurableSpace_atomless σ hσ hinv htotal hf
    (not_ae_constant_of_negInfiniteLogIntegral hnonzero hlog) hs hpos

end Invariant233

end OAI
