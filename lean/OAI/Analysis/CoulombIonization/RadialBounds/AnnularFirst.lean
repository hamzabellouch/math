import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedAnnularCountBarrier
import OAI.Analysis.CoulombIonization.FormDomain.GraphWeightIntegral

namespace OAI

open MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy

lemma probability_first_le_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Integrable (fun x => f x^2) μ)
    (hn : ∀ x, 0 ≤ f x) : (∫ x, f x ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) := by
  have hh := sum_integral_sqrt_mul_sqrt_le (ι := Unit) (fun _ => μ)
    (fun _ x => f x^2) (fun _ _ => (1:ℝ)) (fun _ => hf) (fun _ => integrable_const _)
    (fun _ x => sq_nonneg (f x)) (fun _ _ => zero_le_one)
  simpa only [Fintype.sum_unique,Real.sqrt_sq (hn _),Real.sqrt_one,mul_one,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] using hh

lemma actual_annular_first_bound {Z lam D r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hD : 0 ≤ D) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) lam N) (F : fermionGraph N)
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+D) :
    (∫ x, rawAnnularCount r (2*r) x ∂graphRawLaw F) ≤
      (Classical.choose (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one))*
        annularOffsetMass D r := by
  let C := Classical.choose (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)
  have hC : 1 ≤ C := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hm : formMass (graphFormVector F) = 1 := (formMass_graph F).trans hFn
  have he : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ D :=
    max_le (priced_graph_tilt_excess hN F hFn hFE) hD
  have hh := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).2
    Z lam N (graphFormVector F) (graphFormVector_sobolev F) hm hZ hlam D r hD hr he
  have hh' : rawAnnularMoment (graphFormVector F) r (2*r) ≤ C*1*(annularOffsetMass D r)^2 := by
    calc _ = rawAnnularMoment (graphFormVector F) (1*r) (2*r) := by congr 1; ring
         _ ≤ C*(annularOffsetMass D r)^2 := hh
         _ = _ := by ring
  have hs' := sqrt_count_scale (rawAnnularMoment_nonneg (graphFormVector F) r (2*r)) hC (by norm_num : (0:ℝ)≤1)
    (le_trans zero_le_one (annularOffsetMass_one_le D r)) hh'
  have hs : Real.sqrt (rawAnnularMoment (graphFormVector F) r (2*r)) ≤ C*annularOffsetMass D r :=
    hs'.trans_eq (by rw [Real.sqrt_one]; ring)
  let := graphRawLaw_probability F hFn
  have hi : Integrable (fun x => rawAnnularCount r (2*r) x^2) (graphRawLaw F) :=
    graph_weight_integrable F _ ((rawAnnularCount_measurable _ _).pow_const 2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le _ _ _) 2)
  have hf := probability_first_le_sqrt (rawAnnularCount r (2*r)) hi (rawAnnularCount_nonneg _ _)
  rw [rawAnnularMoment_eq_integral (graphFormVector_sobolev F).sobolevVector,formRawLaw_graph] at hs
  exact hf.trans hs
end CoulombAtom

end

end OAI
