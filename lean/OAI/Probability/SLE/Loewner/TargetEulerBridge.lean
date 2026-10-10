import OAI.Probability.SLE.Loewner.TargetCutoffField
import Mathlib.Analysis.ODE.DiscreteGronwall

namespace OAI

/-! The bounded equation underlying the explicitly prescribed Euler flow.
The cutoff is inactive on any path whose height stays above its threshold. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

lemma cutoffField_eq_reciprocal
    (κ : ℝ) (b : Driver) (j : ℕ) (t : ℝ) (z : ℂ)
    (hcut : (j:ℝ)^(-(4:ℤ)) ≤ ‖z-driverValue b t‖^2) :
    cutoffField κ b j t z = (a κ:ℂ)/(z-driverValue b t) := by
  rw [cutoffField,max_eq_left hcut,mul_div_assoc]
  congr 1
  rw [Complex.inv_def,Complex.normSq_eq_norm_sq]
  simp only [div_eq_mul_inv,starRingEnd_apply,Complex.ofReal_inv]

lemma exists_cutoff_solution
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    ∃ (L K : ℝ≥0) (X : ℝ → ℂ),
      (∀ t w, ‖cutoffField κ b j t w‖ ≤ L) ∧
      (∀ t, LipschitzWith K (cutoffField κ b j t)) ∧
      LipschitzWith L X ∧ X 0=z ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt X (cutoffField κ b j t (X t)) (Ici 0) t) := by
  obtain ⟨L,K,hL,hK⟩ := cutoffField_bounds κ j hj
  let V (t : ℝ) (_ : Unit) (w : ℂ) := cutoffField κ b j t w
  have hF : Measurable (fun p : ℝ × ℂ => cutoffField κ b j p.1 p.2) :=
    (continuous_cutoffField κ b j hj).measurable
  have hpair : Measurable (fun q : (ℝ × Unit) × ℂ => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm : Measurable (fun q : (ℝ × Unit) × ℂ => V q.1.1 q.1.2 q.2) :=
    @Measurable.comp ((ℝ × Unit) × ℂ) (ℝ × ℂ) ℂ inferInstance inferInstance inferInstance
      (fun p => cutoffField κ b j p.1 p.2) (fun q => (q.1.1,q.2)) hF hpair
  have hc (_ : Unit) (w : ℂ) : Continuous (fun t => V t () w) :=
    (continuous_cutoffField κ b j hj).comp (continuous_id.prodMk continuous_const)
  obtain ⟨X,hXm,hXl,hX0,hXd,hXconv⟩ := exists_measurable_global_bounded_ode_picard
    V z L K hm hc (fun _ t => hK b t) (fun _ t w => hL b t w)
  exact ⟨L,K,(fun t => X t ()),hL b,hK b,hXl (),hX0 (),fun t ht => hXd () t ht⟩

end SLEExactGauge.Target

end

end OAI
