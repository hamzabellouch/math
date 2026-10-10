import OAI.Probability.LatticePassage.Model
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Set

noncomputable instance environmentProbability : IsProbabilityMeasure environmentLaw :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : Edge => expMeasure 1)))

theorem edge_marginal (e : Edge) :
    Measure.map (fun ω : Environment => ω e) environmentLaw = expMeasure 1 :=
  Measure.infinitePi_map_eval _ e

theorem independent_edge_weights : iIndepFun (fun e (ω : Environment) => ω e) environmentLaw :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

theorem exponential_positive : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hc : (expMeasure 1 (Iic 0)).toReal = 0 := by
    rw [← measureReal_def, ← cdf_eq_real]
    simp [cdf_expMeasure_eq (r := 1) (by norm_num)]
  have hz : expMeasure 1 (Iic 0) = 0 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
      (by simpa using hc)
  simpa only [ae_iff, not_lt, Iic] using hz

theorem all_edge_weights_positive : ∀ᵐ ω ∂environmentLaw, ∀ e, 0 < ω e := by
  rw [ae_all_iff]
  intro e
  exact (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).quasiMeasurePreserving.ae exponential_positive

theorem all_path_costs_nonnegative :
    ∀ᵐ ω ∂environmentLaw, ∀ x y (p : lattice.Walk x y), 0 ≤ pathCost ω p := by
  filter_upwards [all_edge_weights_positive] with ω hω
  intro x y p
  exact pathCost_nonneg ω (fun e => (hω e).le) p

end CompanionFPP

end OAI
