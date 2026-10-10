import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Vanishing tails of an integrable function outside metric balls -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {f : X → ℝ}

theorem integrable_radial_tail (hf : Integrable f μ) (p : X) :
    Tendsto (fun k : ℕ => ∫ x in (ball p (k:ℝ))ᶜ, f x ∂μ) atTop (nhds 0) := by
  have hanti : Antitone (fun k : ℕ => (ball p (k:ℝ))ᶜ) := by
    intro i j hij
    exact compl_subset_compl.mpr (ball_subset_ball (by exact_mod_cast hij))
  have hempty : (⋂ k : ℕ, (ball p (k:ℝ))ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k,hk⟩ := exists_nat_gt (dist x p)
    have hh := mem_iInter.mp hx k
    exact hh (mem_ball.mpr hk)
  have ht := tendsto_setIntegral_of_antitone
    (fun k : ℕ => (measurableSet_ball : MeasurableSet (ball p (k:ℝ))).compl)
    hanti ⟨0,hf.integrableOn⟩
  simpa only [hempty,setIntegral_empty] using ht

end RegularPointCoordinates

end

end OAI
