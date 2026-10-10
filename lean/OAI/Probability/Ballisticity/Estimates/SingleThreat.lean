import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetThreat

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDropMass_le_budget_bad {d k : ℕ} (e f : Direction d) (ω : Environment d)
    (hreg : ∀ x, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) ≤
      relativeBudgetMass e f h (2*z) π ω +
        tupleBadMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) π ω := by
  let A := MedianTubeFailure (realPosition (step e)) f b H z
  have hI (F : (Fin k → Lattice d) → ℝ) (B : ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ B) : Integrable F π := by
    apply (integrable_const B).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hF x).1]; exact (hF x).2
  have hq := hI (fun x => noDropProduct (realPosition (step e)) x ω) 1
    (fun x => noDropProduct_bounds _ x ω)
  have hm := hI (fun x => (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ) 1
    (fun x => ⟨measureReal_nonneg,by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top (relativeBudgetWordLaw_le_one e f h (2*z) ω x)).trans_eq ENNReal.toReal_one⟩)
  have hb := hI (fun x => ∑ j, relativeBadMass (realPosition (step e)) A ω (x j)) k
    (fun x => sum_relativeBadMass_bounds _ A ω x)
  change _ ≤ (∫ x, (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ ∂π) +
    ∫ x, ∑ j, relativeBadMass (realPosition (step e)) A ω (x j) ∂π
  rw [← integral_add hm hb]
  apply integral_mono hq (hm.add hb)
  intro x
  exact (product_noDrop_le_good_bad _ A (measurableSet_medianTubeFailure _ f b H z) ω x).trans
    (add_le_add (tupleGood_le_relativeBudget e f ω hreg H h hh b z x) le_rfl)

def budgetThreatEvent {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (π : Measure (Fin k → Lattice d)) (s : ℝ) : Set (Environment d) :=
  {ω | ∃ h ≤ H, relativeBudgetMass e f h r π ω < s}

lemma budgetThreatEvent_subset_ae {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) (b : ℕ → ℝ) (z s : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    budgetThreatEvent e f H (2*z) π s ≤ᵐ[environmentLaw ν]
      (({ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} ∪
      {ω | s < tupleBadMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) π ω}) : Set (Environment d)) := by
  filter_upwards [quenched_regularPath_ae ν _ htrans] with ω hω
  rintro ⟨h,hh,hbad⟩
  by_cases hq : (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s
  · exact Or.inl hq
  · right
    have hm := noDropMass_le_budget_bad e f ω hω H h hh b z π
    change s < _
    linarith

lemma single_budget_threat_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] :
    (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
      (environmentLaw ν).real {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} +
      (k:ℝ)*(annealedLaw ν).real (MedianTubeFailure (realPosition (step e)) f b H z ∩ NoDrop (realPosition (step e)) 0)/s := by
  let A := MedianTubeFailure (realPosition (step e)) f b H z
  have hA := measurableSet_medianTubeFailure (realPosition (step e)) f b H z
  have hm := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (budgetThreatEvent_subset_ae ν e f htrans H b z s π))
  have hu := measureReal_union_le (μ := environmentLaw ν)
    {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s}
    {ω | s < tupleBadMass (realPosition (step e)) A π ω}
  apply hm.trans (hu.trans (add_le_add le_rfl ?_))
  have hb := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (environmentLaw ν) fun ω => tupleBadMass_nonneg (realPosition (step e)) A π ω)
    (integrable_sum_relativeBadMass ν (realPosition (step e)) A hA π).integral_prod_left s
  rw [tupleBadMass_mean ν (realPosition (step e)) A hA π] at hb
  apply (le_div_iff₀ hs).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (show {ω | s < tupleBadMass (realPosition (step e)) A π ω} ⊆ {ω | s ≤ tupleBadMass (realPosition (step e)) A π ω} from fun ω h => show s ≤ tupleBadMass (realPosition (step e)) A π ω from (show s < tupleBadMass (realPosition (step e)) A π ω from h).le)) hs.le).trans hb

lemma annealed_noDrop_event_le_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤ (conditionedLaw ν ℓ).real A := by
  have he : annealedLaw ν (NoDrop ℓ 0)*conditionedLaw ν ℓ A = annealedLaw ν (A ∩ NoDrop ℓ 0) := by
    rw [conditionedLaw,Measure.smul_apply,Measure.restrict_apply hA,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  have he' := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul] at he'
  change ((annealedLaw ν) (A ∩ NoDrop ℓ 0)).toReal ≤ _
  rw [← he']
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by exact measureReal_le_one)

lemma annealed_median_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν).real (NoDrop ℓ 0)
    (annealedLaw ν).real (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z ∩ NoDrop ℓ 0) ≤
      (10/p^2)*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z := by
  dsimp only
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hp0 : 0 < (annealedLaw ν).real (NoDrop ℓ 0) := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let A := MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z
  have hA := measurableSet_medianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z
  have ha := annealed_noDrop_event_le_conditioned ν ℓ hp A hA
  have hb := conditioned_median_tube_bound ν e f htrans H hz
  dsimp only at hb
  have hc : ((annealedLaw ν).real (NoDrop ℓ 0))^2/2*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤
      5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z :=
    (mul_le_mul_of_nonneg_left ha (by positivity)).trans hb
  have hi : (annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤
      (5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z) /
      (((annealedLaw ν).real (NoDrop ℓ 0))^2/2) := by
    apply (le_div_iff₀ (show 0 < ((annealedLaw ν).real (NoDrop ℓ 0))^2/2 by positivity)).mpr
    nlinarith only [hc]
  convert hi using 1; dsimp [A,ℓ]
  ring

end DirectionalTransience

end

end OAI
