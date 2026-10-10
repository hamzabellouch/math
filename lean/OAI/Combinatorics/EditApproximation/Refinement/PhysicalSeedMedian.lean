import OAI.Combinatorics.EditApproximation.Probability.Median
import OAI.Combinatorics.EditApproximation.Geometry.Accuracy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementInvariants

namespace OAI

/-! The seed update uses the actual integer ceilings, upper median and clamp.
Copies share an entire table within each run and are independent between runs. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

def finiteMedianSeed {Ω : Type*} (N copies : ℕ) (output : Ω → ℕ) (draws : Fin copies → Ω) : ℕ :=
  min N (upperMedian (List.ofFn fun i => output (draws i)))

theorem ofFn_countP_filter {β : Type*} {copies : ℕ} (output : Fin copies → β) (p : β → Bool) :
    (List.ofFn output).countP p = (univ.filter fun i => p (output i)).card := by
  rw [List.ofFn_eq_map, List.countP_map]
  simpa only [List.toFinset_finRange, Bool.decide_eq_true, Function.comp_def] using
    ((List.nodup_finRange copies).card_eq_countP (P := fun i => p (output i))).symm

theorem finiteMedianSeed_lower {Ω : Type*} (N copies c : ℕ) (hcopies : 0 < copies)
    (hcN : c ≤ N) (output : Ω → ℕ) (hlower : ∀ ω, c ≤ output ω) (draws : Fin copies → Ω) :
    c ≤ finiteMedianSeed N copies output draws := by
  apply le_min hcN
  apply upperMedian_lower _ (by simpa using hcopies.ne')
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact hlower (draws i)

theorem finiteMedianSeed_upper {Ω : Type*} (N copies upper : ℕ) (hcopies : 0 < copies)
    (output : Ω → ℕ) (draws : Fin copies → Ω)
    (hfew : (univ.filter fun i => upper < output (draws i)).card < copies - copies / 2) :
    finiteMedianSeed N copies output draws ≤ upper := by
  apply (min_le_right _ _).trans
  apply upperMedian_upper _ (by simpa using hcopies.ne')
  rw [List.length_ofFn, ofFn_countP_filter]
  simp only [decide_eq_true_eq]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin copies)))
    (p := fun i => upper < output (draws i))
  simp only [card_univ, Fintype.card_fin, not_lt] at hsum
  omega

theorem finiteMedianSeed_failure_bound {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N copies upper : ℕ) (hcopies : 0 < copies)
    (output : Ω → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hsingle : μ.real {ω | upper < output ω} ≤ q) :
    (Measure.pi fun _ : Fin copies => μ).real
      {draws | upper < finiteMedianSeed N copies output draws} ≤
      (2 : ℝ) ^ copies * q ^ (copies - copies / 2) := by
  classical
  let bad : Fin copies → Set (Fin copies → Ω) := fun i => {draws | upper < output (draws i)}
  have hindepFun : iIndepFun (fun i (draws : Fin copies → Ω) => draws i)
      (Measure.pi fun _ : Fin copies => μ) :=
    iIndepFun_pi (μ := fun _ : Fin copies => μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hindep : iIndepSet bad (Measure.pi fun _ : Fin copies => μ) := by
    apply (iIndepSet_iff_meas_biInter (fun _ => (Set.toFinite _).measurableSet)).2
    intro s
    exact hindepFun.meas_biInter (fun i _ =>
      ⟨{ω | upper < output ω}, (Set.toFinite _).measurableSet, rfl⟩)
  have hbad (i : Fin copies) : (Measure.pi fun _ : Fin copies => μ).real (bad i) ≤ q := by
    have hmap := measurePreserving_eval (fun _ : Fin copies => μ) i
    have heq := hmap.measure_preimage ((Set.toFinite {ω | upper < output ω}).measurableSet.nullMeasurableSet)
    have heq' : (Measure.pi fun _ : Fin copies => μ) (bad i) = μ {ω | upper < output ω} := by
      simpa only [bad, Function.eval, Set.preimage, Set.mem_ofPred_eq] using heq
    unfold Measure.real
    rw [heq']
    exact hsingle
  have htail := independent_failure_count_binary_bound (Measure.pi fun _ : Fin copies => μ)
    bad hindep (copies - copies / 2) q hq hbad
  apply (measureReal_mono (μ := Measure.pi fun _ : Fin copies => μ) ?_ (measure_ne_top _ _)).trans
    (by simpa only [Fintype.card_fin] using htail)
  intro draws hfail
  by_contra hfew
  have hfew' : ¬ copies - copies / 2 ≤ (univ.filter fun i => upper < output (draws i)).card := by
    simpa only [bad, Set.mem_ofPred_eq] using hfew
  have hupper := finiteMedianSeed_upper N copies upper hcopies output draws (lt_of_not_ge hfew')
  exact (not_lt_of_ge hupper) hfail

/-- The integer multiplication and ceiling used before the median preserve
both the deterministic lower approximation and a successful copy's upper bound. -/
theorem scaledCopy_rounding (c a : ℕ) (ha : 0 < a) (value : ℚ)
    (hlower : (c : ℚ) / a ≤ value) (hupper : value ≤ 2 * c) :
    c ≤ ⌈(a : ℚ) * value⌉₊ ∧ ⌈(a : ℚ) * value⌉₊ ≤ 2 * a * c := by
  have haQ : (0 : ℚ) < a := Nat.cast_pos.2 ha
  constructor
  · have h := (div_le_iff₀ haQ).1 hlower
    have hceil := Nat.le_ceil ((a : ℚ) * value)
    have hmul : (c : ℚ) ≤ a * value := by simpa only [mul_comm] using h
    exact_mod_cast hmul.trans hceil
  · apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left hupper haQ.le
    push_cast
    nlinarith only [h]

theorem finite_positive_excess_tail {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (value : Ω → ℚ) (c : ℕ) (hc : 0 < c)
    (ell : ℝ) (_hell : 0 < ell)
    (hexcess : (∫ ω, max ((value ω : ℝ) - c) 0 ∂μ) ≤ (1 / ell) * c) :
    μ.real {ω | 2 * (c : ℚ) < value ω} ≤ 1 / ell := by
  let excess := fun ω => max ((value ω : ℝ) - c) 0
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => le_max_right ((value ω : ℝ) - c) 0))
    (show Integrable excess μ from .of_finite) (c : ℝ)
  have hcr : (0 : ℝ) < c := Nat.cast_pos.2 hc
  have htail : μ.real {ω | (c : ℝ) ≤ excess ω} ≤ 1 / ell := by
    apply (mul_le_mul_iff_left₀ hcr).mp
    simpa only [mul_comm] using hmarkov.trans hexcess
  apply (measureReal_mono (μ := μ) ?_).trans htail
  intro ω hω
  have hR : 2 * (c : ℝ) < value ω := by exact_mod_cast hω
  exact (by dsimp only [excess]; exact (by linarith : (c : ℝ) ≤ (value ω : ℝ) - c).trans (le_max_left _ _))

noncomputable def physicalScaledCopy {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S : ℕ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (state : PhysicalEntry M J target.length) : ℕ :=
  ⌈(a : ℚ) * physicalRefinement source target U N P F A T delta choices state.1 S state.2⌉₊

theorem physicalScaledCopy_lower {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ) (a S : ℕ)
    (ha : (a : ℚ) = refinementFactor A F)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (state : PhysicalEntry M J target.length) :
    stateEditCost (physicalSource source state.1) target state.2 ≤
      physicalScaledCopy source target U N P F A T delta a S choices state := by
  have haQ : (0 : ℚ) < a := by
    rw [ha]
    exact lt_of_lt_of_le zero_lt_one (refinementFactor_spec A F (by omega)).1
  have hinv := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices state.1 S state.2).1
  have hlower : (stateEditCost (physicalSource source state.1) target state.2 : ℝ) /
      (a : ℝ) ≤ (physicalRefinement source target U N P F A T delta choices state.1 S state.2 : ℝ) := by
    have h := (le_max_left _ _).trans hinv
    simpa only [physicalLower, ← ha, Rat.cast_natCast] using h
  have hlowerQ : (stateEditCost (physicalSource source state.1) target state.2 : ℚ) / a ≤
      physicalRefinement source target U N P F A T delta choices state.1 S state.2 := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div, Rat.cast_natCast] using hlower
  have hm := (div_le_iff₀ haQ).1 hlowerQ
  have hc := Nat.le_ceil ((a : ℚ) * physicalRefinement source target U N P F A T delta choices state.1 S state.2)
  have hm' : (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤
      a * physicalRefinement source target U N P F A T delta choices state.1 S state.2 := by
    simpa only [mul_comm] using hm
  have hscaled : (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤
      (physicalScaledCopy source target U N P F A T delta a S choices state : ℚ) := hm'.trans hc
  exact_mod_cast hscaled

end EditApproximation

end OAI
