import OAI.Combinatorics.Progressions.Probability.RetainedJointUnitLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem jointAffineJetDensity_retained_conditioned_law {W T Q Z X K α : Type*}
    [MeasurableSpace W] [MeasurableSpace T] [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (μ : Measure W) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (z : W → T → Z → ℝ) (hz : ∀ j, Measurable (fun p : W × T => z p.1 p.2 j))
    (x : W → T → X → ℝ) (hx : ∀ j, Measurable (fun p : W × T => x p.1 p.2 j)) :
    ((μ.prod (jointUnitCoefficientSource J N)).prod ν).map
      (fun p => (p.1.1, jointAffineJetUnitMap s A F e input (z p.1.1 p.2) rows c w (x p.1.1 p.2) p.1.2)) =
      realDensityMeasure (μ.prod volume)
        (fun p => densityMixture ν
          (fun t => jointAffineJetDensity s A F e input (z p.1 t) rows c w (x p.1 t)) p.2) := by
  let U := fun p : W × ((∀ q, J q ⊕ N q → ℝ) × T) =>
    jointAffineJetUnitMap s A F e input (z p.1 p.2.2) rows c w (x p.1 p.2.2) p.2.1
  have hU : Measurable U :=
    jointAffineJetUnitMap_measurable_comp (Ω := W × ((∀ q, J q ⊕ N q → ℝ) × T)) s A F e input rows
      (fun _ => c) (fun _ => w) (fun p => p.2.1)
      (fun _ => measurable_const) (fun _ => measurable_const)
      (fun q => (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))
      (fun p => z p.1 p.2.2) (fun j => (hz j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (fun p => x p.1 p.2.2) (fun j => (hx j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exact (product_image_law_assoc μ (jointUnitCoefficientSource J N) ν (fun p => (p.1, U p))
    (measurable_fst.prodMk hU)).trans
    (jointAffineJetDensity_retained_unit_law s A F e input rows c w hw R hsupport μ ν z hz x hx)

end Erdos3

end

end OAI
