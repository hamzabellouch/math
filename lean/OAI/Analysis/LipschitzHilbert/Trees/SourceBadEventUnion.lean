import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceTailOrder
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! The finitely many deterministic residual events may be combined
before selecting a spatial point or a mass cutoff. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

/-- Fixed polynomial losses are absorbed by one extra unit in the
exponential decay rate. -/
theorem eventually_source_polynomial_exp (C a J : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, C*L^a*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 (by norm_num : (0:ℝ) < 1)
  filter_upwards [hdecay.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 1/C))] with L hL
  have hsmall : C*(L^a*Real.exp (-L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hL.le hC.le
    have heq : C*(1/C) = 1 := by field_simp
    simpa only [one_mul,neg_mul,heq] using h
  calc
    _ = (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) := by
      rw [show (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) =
        C*L^a*(Real.exp (-L)*Real.exp (-J*L)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ 1*Real.exp (-J*L) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Union measure on an actual interval, with the exact number of
square/error/shift events retained until exponential absorption. -/
theorem source_bad_event_union {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (events : Finset ι) (bad : ι → Set X) (δ : ℝ)
    (htail : ∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal δ*μ univ) :
    μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal ((events.card:ℝ)*δ)*μ univ := by
  calc
    _ ≤ ∑ i ∈ events, μ (bad i) := measure_biUnion_finset_le events bad
    _ ≤ ∑ _i ∈ events, ENNReal.ofReal δ*μ univ := Finset.sum_le_sum htail
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg events.card)]
      norm_cast
      ring


/-- The polynomial number of shift events loses one unit of exponential
rate, uniformly in all measurable spaces and finite event lists. -/
theorem eventually_source_bad_event_tail (a J : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι X : Type*) [MeasurableSpace X]
      (μ : Measure X) (events : Finset ι) (bad : ι → Set X),
      (events.card:ℝ) ≤ L^a →
      (∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*μ univ) →
      μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal (Real.exp (-J*L))*μ univ := by
  filter_upwards [eventually_source_polynomial_exp 1 a J (by norm_num)] with L hL
  intro ι X _ μ events bad hcard htail
  apply (source_bad_event_union μ events bad (Real.exp (-(J+1)*L)) htail).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans
    (by simpa only [one_mul] using hL)

end LipschitzHilbert

end

end OAI
