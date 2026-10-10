import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMeasureWeak
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

namespace OAI

/-! # Finite products of the logarithmic prime measures -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_pi_mass_normalize {ι : Type*} [Fintype ι]
    (μ : ι → FiniteMeasure ℝ) :
    FiniteMeasure.pi μ = (∏ i, (μ i).mass) •
      (ProbabilityMeasure.pi (fun i => (μ i).normalize)).toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : (∏ i, (μ i).mass) * (∏ i, (μ i).normalize (s i)) = ∏ i, μ i (s i) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun i _ => ((μ i).self_eq_mass_mul_normalize (s i)).symm)
  simp only [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_pi, Measure.coe_nnreal_smul_apply, Measure.pi_pi,
    ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

theorem primeLogProduct_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (h : ℕ) :
    Tendsto (fun x => FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) atTop
      (𝓝 (FiniteMeasure.pi (fun _ : Fin h => logarithmicPrimeMeasure c))) := by
  have ht := primeLogMeasure_tendsto hc hc1
  have hm0 : logarithmicPrimeMeasure c ≠ 0 := by
    intro hz
    have hm := logarithmicPrimeMeasure_mass hc hc1.le
    rw [hz, FiniteMeasure.zero_mass, NNReal.coe_zero] at hm
    linarith [Real.log_neg hc hc1]
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto ht hm0
  have hp : Tendsto (fun x => ProbabilityMeasure.pi (fun _ : Fin h => (primeLogMeasure c x).normalize))
      atTop (𝓝 (ProbabilityMeasure.pi (fun _ : Fin h => (logarithmicPrimeMeasure c).normalize))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun _ => hn))
  have hm := tendsto_finsetProd (univ : Finset (Fin h)) (fun _ _ => ht.mass)
  have hh := hm.smul (ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp hp)
  simpa only [Function.comp_apply, ← finiteMeasure_pi_mass_normalize] using hh

theorem finiteMeasure_set_tendsto {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [Nonempty Ω]
    {F : Filter ι} {μ : ι → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hμ : Tendsto μ F (𝓝 ν)) (hν : ν ≠ 0) {s : Set Ω}
    (hs : ν (frontier s) = 0) : Tendsto (fun x => μ x s) F (𝓝 (ν s)) := by
  have hs' : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν, hs, mul_zero]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hμ hν) hs'
  have hh := hμ.mass.mul ht
  simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hh

end JointDickman

end OAI
