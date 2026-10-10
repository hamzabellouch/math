import OAI.Combinatorics.Progressions.Lattices.JointAffineUnitSource
import OAI.Combinatorics.Progressions.Probability.SourceOrderImageLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T Q Z X K α : Type*} [MeasurableSpace T] [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (μ : Measure T) [IsProbabilityMeasure μ]
    (z : T → Z → ℝ) (hz : ∀ j, Measurable (fun t => z t j))
    (x : T → X → ℝ) (hx : ∀ j, Measurable (fun t => x t j))

include hw hsupport hz hx

theorem jointAffineJetDensity_unit_mixture_law :
    (μ.prod (jointUnitCoefficientSource J N)).map
      (fun p => jointAffineJetUnitMap s A F e input (z p.1) rows c w (x p.1) p.2) =
      realDensityMeasure volume
        (densityMixture μ (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t))) := by
  have hU := jointAffineJetUnitMap_measurable_comp (Ω := T × (∀ q, J q ⊕ N q → ℝ))
    s A F e input rows (fun _ => c) (fun _ => w) (fun p => p.2)
    (fun _ => measurable_const) (fun _ => measurable_const)
    (fun q => (measurable_pi_apply q).comp measurable_snd)
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
    (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
  have hm := jointAffineJetDensity_measurable_comp (Ω := T × (∀ q, I q → ℝ))
    s A F e input rows c w hw R hsupport
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
    (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
    (fun p => p.2) (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
  apply densityMixture_image_law μ (jointUnitCoefficientSource J N) volume _ hU
    (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t)) hm
  · intro t
    have hp := jointAffineJetDensity_probability_data s A F e input (z t) rows c w hw R hsupport (x t)
    exact ⟨hp.2.1, hp.1, hp.2.2⟩
  · intro t
    exact jointAffineJetDensity_unit_law s A F e input (z t) rows c w hw R hsupport (x t)

theorem jointAffineJetDensity_unit_mixture_law_swapped :
    ((jointUnitCoefficientSource J N).prod μ).map
      (fun p => jointAffineJetUnitMap s A F e input (z p.2) rows c w (x p.2) p.1) =
      realDensityMeasure volume
        (densityMixture μ (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t))) := by
  have hU := jointAffineJetUnitMap_measurable_comp (Ω := T × (∀ q, J q ⊕ N q → ℝ))
    s A F e input rows (fun _ => c) (fun _ => w) (fun p => p.2)
    (fun _ => measurable_const) (fun _ => measurable_const)
    (fun q => (measurable_pi_apply q).comp measurable_snd)
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
    (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
  exact (product_image_law_swap μ (jointUnitCoefficientSource J N) _ hU).trans
    (jointAffineJetDensity_unit_mixture_law s A F e input rows c w hw R hsupport μ z hz x hx)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem jointAffineJetDensity_retained_unit_law {W T Q Z X K α : Type*}
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
    (μ.prod ((jointUnitCoefficientSource J N).prod ν)).map
      (fun p => (p.1, jointAffineJetUnitMap s A F e input (z p.1 p.2.2) rows c w (x p.1 p.2.2) p.2.1)) =
      realDensityMeasure (μ.prod volume)
        (fun p => densityMixture ν
          (fun t => jointAffineJetDensity s A F e input (z p.1 t) rows c w (x p.1 t)) p.2) := by
  let D := fun a => densityMixture ν
    (fun t => jointAffineJetDensity s A F e input (z a t) rows c w (x a t))
  let U := fun p : W × ((∀ q, J q ⊕ N q → ℝ) × T) =>
    jointAffineJetUnitMap s A F e input (z p.1 p.2.2) rows c w (x p.1 p.2.2) p.2.1
  have hU : Measurable U :=
    jointAffineJetUnitMap_measurable_comp (Ω := W × ((∀ q, J q ⊕ N q → ℝ) × T)) s A F e input rows
      (fun _ => c) (fun _ => w) (fun p => p.2.1)
      (fun _ => measurable_const) (fun _ => measurable_const)
      (fun q => (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))
      (fun p => z p.1 p.2.2) (fun j => (hz j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (fun p => x p.1 p.2.2) (fun j => (hx j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hD : Measurable (Function.uncurry D) := by
    have hm := jointAffineJetDensity_measurable_comp (Ω := (W × (∀ q, I q → ℝ)) × T)
      s A F e input rows c w hw R hsupport
      (fun p => z p.1.1 p.2) (fun j => (hz j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p => x p.1.1 p.2) (fun j => (hx j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p => p.1.2) (fun q i => (measurable_pi_apply i).comp
        ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  apply retainedDensity_image_law μ ((jointUnitCoefficientSource J N).prod ν) volume U hU D hD
  · intro a
    have hm := jointAffineJetDensity_measurable_comp (Ω := T × (∀ q, I q → ℝ))
      s A F e input rows c w hw R hsupport
      (fun p => z a p.1) (fun j => (hz j).comp (measurable_const.prodMk measurable_fst))
      (fun p => x a p.1) (fun j => (hx j).comp (measurable_const.prodMk measurable_fst))
      (fun p => p.2) (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
    exact densityMixture_probability_density ν volume
      (fun t => jointAffineJetDensity s A F e input (z a t) rows c w (x a t)) hm
      (Filter.Eventually.of_forall (fun t => by
        have hp := jointAffineJetDensity_probability_data s A F e input (z a t) rows c w hw R hsupport (x a t)
        exact ⟨hp.2.1, hp.1, hp.2.2⟩))
  · intro a
    exact jointAffineJetDensity_unit_mixture_law_swapped s A F e input rows c w hw R hsupport ν
      (z a) (fun j => (hz j).comp (measurable_const.prodMk measurable_id))
      (x a) (fun j => (hx j).comp (measurable_const.prodMk measurable_id))

end Erdos3

end

end OAI
