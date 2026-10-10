import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricContinuity
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.RingTheory.TwoSidedIdeal.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal

variable {ι : Type*} {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)]
variable (T : ∀ i, PositiveQuasitrace (D i)) (F : Filter ι)

def IsFilteredQuasitraceNull (u : ∀ i, D i) : Prop :=
  Tendsto (fun i => (T i).metricSize (u i)) F (nhds 0)

lemma isFilteredQuasitraceNull_iff_square (u : ∀ i, D i) :
    IsFilteredQuasitraceNull T F u ↔
      Tendsto (fun i => T i (Positive.starMul (u i))) F (nhds 0) := by
  constructor
  · intro h
    simpa only [PositiveQuasitrace.metricSize_cube, zero_pow (by decide : 3 ≠ 0)] using h.pow 3
  · intro h
    have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (3 : ℝ)⁻¹)).tendsto 0
    simpa [IsFilteredQuasitraceNull, PositiveQuasitrace.metricSize, Function.comp_def] using hc.comp h

lemma isFilteredQuasitraceNull_zero : IsFilteredQuasitraceNull T F (fun _ => 0) := by
  simp only [IsFilteredQuasitraceNull, PositiveQuasitrace.metricSize_zero]
  exact tendsto_const_nhds

lemma isFilteredQuasitraceNull_neg {u : ∀ i, D i}
    (h : IsFilteredQuasitraceNull T F u) :
    IsFilteredQuasitraceNull T F (fun i => -u i) := by
  simpa only [IsFilteredQuasitraceNull, PositiveQuasitrace.metricSize_neg] using h

lemma isFilteredQuasitraceNull_star {u : ∀ i, D i}
    (h : IsFilteredQuasitraceNull T F u) :
    IsFilteredQuasitraceNull T F (fun i => star (u i)) := by
  simpa only [IsFilteredQuasitraceNull, PositiveQuasitrace.metricSize_star] using h

lemma isFilteredQuasitraceNull_mul_left {u v : ∀ i, D i}
    (hv : IsFilteredQuasitraceNull T F v) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ i, ‖u i‖ ≤ C) :
    IsFilteredQuasitraceNull T F (fun i => u i * v i) := by
  refine squeeze_zero (fun i => (T i).metricSize_nonneg _) (fun i => ?_)
    (show Tendsto (fun i => C^(2/3:ℝ) * (T i).metricSize (v i)) F (nhds 0) by
      simpa using hv.const_mul (C^(2/3:ℝ)))
  exact ((T i).metricSize_mul_le_left _ _).trans (mul_le_mul
    (Real.rpow_le_rpow (norm_nonneg _) (hu i) (by norm_num)) le_rfl
    ((T i).metricSize_nonneg _) (Real.rpow_nonneg hC _))

lemma isFilteredQuasitraceNull_mul_right {u v : ∀ i, D i}
    (hu : IsFilteredQuasitraceNull T F u) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ C) :
    IsFilteredQuasitraceNull T F (fun i => u i * v i) := by
  have h := isFilteredQuasitraceNull_mul_left T F
    (isFilteredQuasitraceNull_star T F hu) C hC
    (show ∀ i, ‖star (v i)‖ ≤ C by simpa using hv)
  simpa only [← star_mul, IsFilteredQuasitraceNull, PositiveQuasitrace.metricSize_star] using h

variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x + (T i).metricSize y)

include hadd in
lemma isFilteredQuasitraceNull_add {u v : ∀ i, D i}
    (hu : IsFilteredQuasitraceNull T F u) (hv : IsFilteredQuasitraceNull T F v) :
    IsFilteredQuasitraceNull T F (fun i => u i + v i) :=
  squeeze_zero (fun i => (T i).metricSize_nonneg _) (fun i => hadd i _ _)
    (by simpa using hu.add hv)

def filteredQuasitraceNullIdeal : TwoSidedIdeal (lp D ∞) :=
  TwoSidedIdeal.mk' {u | IsFilteredQuasitraceNull T F (fun i => u i)}
    (isFilteredQuasitraceNull_zero T F)
    (fun hu hv => isFilteredQuasitraceNull_add T F hadd hu hv)
    (fun hu => isFilteredQuasitraceNull_neg T F hu)
    (fun {left _} hright => isFilteredQuasitraceNull_mul_left T F hright ‖left‖ (norm_nonneg _)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero left))
    (fun {_ right} hleft => isFilteredQuasitraceNull_mul_right T F hleft ‖right‖ (norm_nonneg _)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero right))

lemma filteredQuasitraceNullIdeal_mem_null (u : lp D ∞) :
    u ∈ filteredQuasitraceNullIdeal T F hadd ↔
      IsFilteredQuasitraceNull T F (fun i => u i) :=
  TwoSidedIdeal.mem_mk' (R := lp D ∞) _ _ _ _ _ _ u

lemma filteredQuasitraceNullIdeal_mem (u : lp D ∞) :
    u ∈ filteredQuasitraceNullIdeal T F hadd ↔
      Tendsto (fun i => T i (Positive.starMul (u i))) F (nhds 0) :=
  by
    exact (filteredQuasitraceNullIdeal_mem_null T F hadd u).trans
      (isFilteredQuasitraceNull_iff_square T F _)

lemma filteredQuasitraceNullIdeal_star {u : lp D ∞}
    (hu : u ∈ filteredQuasitraceNullIdeal T F hadd) :
    star u ∈ filteredQuasitraceNullIdeal T F hadd :=
  by
    rw [filteredQuasitraceNullIdeal_mem_null] at hu ⊢
    exact isFilteredQuasitraceNull_star T F hu

lemma family_exists_norm_delta (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ i (x : D i), ‖x‖ < δ → (T i).metricSize x < ε := by
  have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (2/3:ℝ))).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc ε hε
  refine ⟨δ, hδ, fun i x hx => ?_⟩
  have hb := (T i).metricSize_le_norm x
  have h1 : (T i).metricSize 1 = 1 := by
    simp [PositiveQuasitrace.metricSize, Positive.starMul, hunit i]
  rw [h1, mul_one] at hb
  have hr := h (show dist ‖x‖ 0 < δ by simpa using hx)
  have hz : (0 : ℝ) ^ (2/3:ℝ) = 0 := by norm_num
  rw [hz, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hr
  exact hb.trans_lt hr

lemma filteredQuasitraceNullIdeal_isClosed
    (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1) :
    IsClosed (filteredQuasitraceNullIdeal T F hadd : Set (lp D ∞)) := by
  apply isClosed_of_closure_subset
  intro u hu
  change u ∈ filteredQuasitraceNullIdeal T F hadd
  rw [filteredQuasitraceNullIdeal_mem_null]
  rw [IsFilteredQuasitraceNull, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hδsize⟩ := family_exists_norm_delta T hunit (ε/2) (half_pos hε)
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu δ hδ
  have hnear (i : ι) : (T i).metricSize (u i-v i) < ε/2 := by
    apply hδsize
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) i).trans_lt
      (by simpa only [dist_eq_norm] using huv)
  have hv' := (filteredQuasitraceNullIdeal_mem_null T F hadd v).mp hv
  have he := (Metric.tendsto_nhds.mp hv') (ε/2) (half_pos hε)
  filter_upwards [he] with i hi
  have hi' : (T i).metricSize (v i) < ε/2 := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ((T i).metricSize_nonneg _)] using hi
  have ht := hadd i (u i-v i) (v i)
  rw [sub_add_cancel] at ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg ((T i).metricSize_nonneg _)]
  linarith [hnear i]

lemma filteredQuasitraceNullIdeal_one_not_mem [∀ i, Nontrivial (D i)] [F.NeBot]
    (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1) :
    (1 : lp D ∞) ∉ filteredQuasitraceNullIdeal T F hadd := by
  rw [filteredQuasitraceNullIdeal_mem]
  have he (i : ι) : T i (Positive.starMul ((1 : lp D ∞) i)) = 1 := by
    simpa [Positive.starMul] using hunit i
  simp only [he]
  intro h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)
end CuntzPureness

end

end OAI
