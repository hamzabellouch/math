import OAI.Analysis.Pureness.Quasitrace.QuasitraceFilteredQuotient
import Mathlib.Topology.Order.Compact

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {ι : Type*} {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)]
variable (T : ∀ i, PositiveQuasitrace (D i)) (U : Ultrafilter ι)
variable (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)

def quasitraceUltraSize (u : lp D ∞) : ℝ :=
  limUnder (U : Filter ι) (fun i => (T i).metricSize (u i))

include hunit

lemma quasitraceUltraSize_tendsto (u : lp D ∞) :
    Tendsto (fun i => (T i).metricSize (u i)) (U : Filter ι)
      (nhds (quasitraceUltraSize T U u)) := by
  apply tendsto_nhds_limUnder
  let g : ι → ℝ := fun i => (T i).metricSize (u i)
  have hg (i : ι) : g i ∈ Set.Icc 0 (‖u‖^(2/3:ℝ)) := by
    refine ⟨(T i).metricSize_nonneg _, ?_⟩
    have h1 : (T i).metricSize 1 = 1 := by
      simp [PositiveQuasitrace.metricSize, Positive.starMul, hunit i]
    have hb := (T i).metricSize_le_norm (u i)
    rw [h1, mul_one] at hb
    exact hb.trans (Real.rpow_le_rpow (norm_nonneg _)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u i) (by norm_num))
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds' (U.map g)
    (show Set.Icc 0 (‖u‖^(2/3:ℝ)) ∈ U.map g from by
      change {i | g i ∈ Set.Icc 0 (‖u‖^(2/3:ℝ))} ∈ U
      exact Filter.Eventually.of_forall hg)
  exact ⟨r, hr⟩

lemma quasitraceUltraSize_nonneg (u : lp D ∞) : 0 ≤ quasitraceUltraSize T U u :=
  ge_of_tendsto (quasitraceUltraSize_tendsto T U hunit u)
    (Filter.Eventually.of_forall fun i => (T i).metricSize_nonneg _)

lemma quasitraceUltraSize_norm_le (u : lp D ∞) :
    quasitraceUltraSize T U u ≤ ‖u‖^(2/3:ℝ) := by
  apply le_of_tendsto (quasitraceUltraSize_tendsto T U hunit u)
  filter_upwards [] with i
  have h1 : (T i).metricSize 1 = 1 := by
    simp [PositiveQuasitrace.metricSize, Positive.starMul, hunit i]
  have hb := (T i).metricSize_le_norm (u i)
  rw [h1, mul_one] at hb
  exact hb.trans (Real.rpow_le_rpow (norm_nonneg _)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u i) (by norm_num))

lemma quasitraceUltraSize_zero : quasitraceUltraSize T U (0 : lp D ∞) = 0 := by
  apply tendsto_nhds_unique (quasitraceUltraSize_tendsto T U hunit 0)
  change Tendsto (fun i => (T i).metricSize 0) (U : Filter ι) (nhds 0)
  simp only [PositiveQuasitrace.metricSize_zero]
  exact tendsto_const_nhds

lemma quasitraceUltraSize_neg (u : lp D ∞) :
    quasitraceUltraSize T U (-u) = quasitraceUltraSize T U u := by
  apply tendsto_nhds_unique (quasitraceUltraSize_tendsto T U hunit (-u))
  change Tendsto (fun i => (T i).metricSize (-u i)) (U : Filter ι) _
  simpa only [PositiveQuasitrace.metricSize_neg] using
    quasitraceUltraSize_tendsto T U hunit u

lemma quasitraceUltraSize_star (u : lp D ∞) :
    quasitraceUltraSize T U (star u) = quasitraceUltraSize T U u := by
  apply tendsto_nhds_unique (quasitraceUltraSize_tendsto T U hunit (star u))
  simpa only [lp.star_apply, PositiveQuasitrace.metricSize_star] using
    quasitraceUltraSize_tendsto T U hunit u

lemma quasitraceUltraSize_one [∀ index, Nontrivial (D index)] :
    quasitraceUltraSize T U (1 : lp D ∞) = 1 := by
  apply tendsto_nhds_unique (quasitraceUltraSize_tendsto T U hunit 1)
  have he (i : ι) : (T i).metricSize ((1 : lp D ∞) i) = 1 := by
    simp [PositiveQuasitrace.metricSize, Positive.starMul, hunit i]
  simp only [he]
  exact tendsto_const_nhds

variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x + (T i).metricSize y)

include hadd in
lemma quasitraceUltraSize_add (u v : lp D ∞) :
    quasitraceUltraSize T U (u+v) ≤ quasitraceUltraSize T U u + quasitraceUltraSize T U v :=
  le_of_tendsto_of_tendsto (quasitraceUltraSize_tendsto T U hunit (u+v))
    ((quasitraceUltraSize_tendsto T U hunit u).add (quasitraceUltraSize_tendsto T U hunit v))
    (Filter.Eventually.of_forall fun i => hadd i _ _)

lemma quasitraceUltraSize_eq_zero (u : lp D ∞) :
    quasitraceUltraSize T U u = 0 ↔ u ∈ filteredQuasitraceNullIdeal T (U : Filter ι) hadd := by
  rw [filteredQuasitraceNullIdeal_mem_null]
  constructor
  · intro h
    simpa only [h, IsFilteredQuasitraceNull] using quasitraceUltraSize_tendsto T U hunit u
  · intro h
    exact tendsto_nhds_unique (quasitraceUltraSize_tendsto T U hunit u) h

lemma quasitraceUltraSize_congr (u v : lp D ∞)
    (h : (filteredQuasitraceNullIdeal T (U : Filter ι) hadd).ringCon u v) :
    quasitraceUltraSize T U u = quasitraceUltraSize T U v := by
  rw [TwoSidedIdeal.rel_iff] at h
  have hz := (quasitraceUltraSize_eq_zero T U hunit hadd (u-v)).mpr h
  have h1 := quasitraceUltraSize_add T U hunit hadd (u-v) v
  have h2 := quasitraceUltraSize_add T U hunit hadd (-(u-v)) u
  rw [sub_add_cancel,hz,zero_add] at h1
  rw [neg_sub,sub_add_cancel] at h2
  have hrev : quasitraceUltraSize T U (v-u) = 0 := by
    rw [← neg_sub u v, quasitraceUltraSize_neg T U hunit, hz]
  rw [hrev,zero_add] at h2
  exact le_antisymm h1 h2

variable [∀ index, Nontrivial (D index)]

def ultraproductQuasitraceSize : FilteredQuasitraceQuotient T (U : Filter ι) hadd hunit → ℝ :=
  Quotient.lift (quasitraceUltraSize T U) (quasitraceUltraSize_congr T U hunit hadd)

lemma ultraproductQuasitraceSize_map (u : lp D ∞) :
    ultraproductQuasitraceSize T U hunit hadd
      (filteredQuasitraceQuotientMap T (U : Filter ι) hadd hunit u) = quasitraceUltraSize T U u := rfl

lemma ultraproductQuasitraceSize_eq_zero
    (x : FilteredQuasitraceQuotient T (U : Filter ι) hadd hunit) :
    ultraproductQuasitraceSize T U hunit hadd x = 0 ↔ x = 0 := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal T (U : Filter ι) hadd hunit).quotientMap_surjective x
  change quasitraceUltraSize T U u = 0 ↔
    (filteredQuasitraceNullIdeal T (U : Filter ι) hadd).ringCon.mk' u =
      (filteredQuasitraceNullIdeal T (U : Filter ι) hadd).ringCon.mk' 0
  constructor
  · intro h
    exact Quotient.sound ((quasitraceUltraSize_eq_zero T U hunit hadd u).mp h)
  · intro h
    exact (quasitraceUltraSize_eq_zero T U hunit hadd u).mpr (Quotient.exact h)
end CuntzPureness

end

end OAI
