import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductMeasure

namespace OAI

/-! # Null boundaries for the prime-product cutoffs -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

instance logarithmicPrimeMeasure_nullSingletons (c : ℝ) :
    NullSingletonClass (logarithmicPrimeMeasure c : Measure ℝ) := by
  constructor
  intro t
  change (Measure.map Real.exp (volume.restrict (Set.Ioc (Real.log c) 0))) {t} = 0
  rw [Measure.map_apply Real.measurable_exp (measurableSet_singleton t),
    Measure.restrict_apply (Real.measurable_exp (measurableSet_singleton t))]
  apply measure_mono_null (t := {Real.log t}) _ (measure_singleton _)
  rintro y ⟨hy,_⟩
  have he : Real.exp y = t := hy
  simpa only [Real.log_exp, Set.mem_singleton_iff] using (congrArg Real.log he)

theorem pi_sum_level_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | ∑ i, t i = a} = 0 := by
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 + ∑ i, t.2 i = a}
  have hE : MeasurableSet E := by
    apply isClosed_eq _ continuous_const |>.measurableSet
    exact continuous_fst.add (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd))
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      {t | ∑ i, t i = a} := by
    ext t
    change t 0 + ∑ i : Fin n, t ((0 : Fin (n+1)).succAbove i) = a ↔ ∑ i, t i = a
    rw [Fin.sum_univ_succAbove t 0]
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf : ∀ t : Fin n → ℝ, (fun x : ℝ => (x,t)) ⁻¹' E = {a - ∑ i, t i} := by
    intro t
    ext x
    change x + ∑ i, t i = a ↔ x = a - ∑ i, t i
    constructor <;> intro h <;> linarith
  simp only [hf, measure_singleton, lintegral_zero]

theorem pi_sum_sublevel_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier {t | ∑ i, t i ≤ a}) = 0 := by
  have hcont : Continuous (fun t : Fin (n+1) → ℝ => ∑ i, t i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  apply measure_mono_null (t := {t | ∑ i, t i = a}) _ (pi_sum_level_null μ n a)
  intro t ht
  have hh := hcont.frontier_preimage_subset (Set.Iic a) ht
  change ∑ i, t i = a
  simpa only [frontier_Iic, Set.mem_preimage, Set.mem_singleton_iff] using hh

theorem primeLogProduct_sublevel_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a : ℝ) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      {t | ∑ i, t i ≤ a} : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        {t | ∑ i, t i ≤ a} : ℝ)) := by
  have hmass : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hp : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hmass)
  apply NNReal.tendsto_coe.mpr
  apply finiteMeasure_set_tendsto (primeLogProduct_tendsto hc hc1 (n+1)) hp
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  exact pi_sum_sublevel_null_frontier _ n a

end JointDickman

end OAI
