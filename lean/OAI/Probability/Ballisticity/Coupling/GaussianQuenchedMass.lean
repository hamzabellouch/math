import Mathlib
import OAI.Probability.Ballisticity.Coupling.QuenchedSuccessComparison
import OAI.Probability.Ballisticity.Walk.PathWindowTest
import OAI.Probability.Ballisticity.Coupling.GaussianQuenchedTube
import OAI.Probability.Ballisticity.Estimates.ProbabilityLowerTransfer

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma quenched_gaussian_success_tube_from_test {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (2/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (ρ δ B : ℝ) (hδ : 0 < δ) (F : C(unitInterval,ℝ) →ᵇ ℝ)
    (hF : ∀ g, 0 ≤ F g ∧ F g ≤ 1)
    (hFs : ∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval,
      dist t (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval) ≤ δ → |g t| < ρ)
    (hb : 0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (bStar : ℕ → ℝ) (hbStar : Tendsto bStar atTop atTop) (x : Lattice d) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    Tendsto (fun i => (environmentLaw ν).real {ω |
      (successQuenchedKernel ℓ x (⌊n i⌋₊:ℝ) ω).real
        (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) <
          (∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/4}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let H := fun i => ⌊n i⌋₊
  let A := fun i => medianTubeEndpoint ν ℓ hp f x (H i) (bStar i*r i) (ρ*r i)
  let p := fun i ω => (noDropQuenchedKernel ℓ x ω).real (A i)
  let q := fun i ω => (successQuenchedKernel ℓ x (H i) ω).real (A i)
  let cost := fun i ω => 1-(noDropQuenched ℓ x ω/crossingQuenched ℓ x (H i) ω).toReal
  have hm (i : ℕ) : Measurable (cost i) := measurable_const.sub
    ((measurable_noDropQuenched ℓ x).div (measurable_crossingQuenched ℓ x (H i))).ennreal_toReal
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
  have hc : TendstoInMeasure (environmentLaw ν) cost atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun i => (hm i).aestronglyMeasurable)
      (noDrop_success_cost_ae_tendsto ν hue ℓ (signed_direction_unit e) htrans x H hH)
  have hbound (i : ℕ) : ∀ᵐ ω ∂environmentLaw ν, |p i ω-q i ω| ≤ cost i ω := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ (signed_direction_unit e) htrans,
      quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hq hs
    exact quenched_success_event_comparison ℓ x (H i) ω (ne_of_gt (hq x)) (hs x (H i))
      (A i) (measurableSet_medianTubeEndpoint ν ℓ hp f x _ _ _)
  have hh := probability_lower_transfer (environmentLaw ν) p q cost
    ((∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/2) (half_pos hb)
    (quenched_gaussian_noDrop_tube_from_test ν hue e f hef htrans W hW ρ δ B hδ F hF hFs hb r hr bStar hbStar x)
    hc hbound
  simpa only [div_div,show (2:ℝ)*2=4 by norm_num] using hh

theorem gaussian_quenched_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ → ℝ,
      IsGaussianSequence (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r →
      ∀ bStar : ℕ → ℝ, Tendsto bStar atTop atTop → ∀ x : Lattice d,
      let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
      Tendsto (fun i => (environmentLaw ν).real {ω |
        (successQuenchedKernel ℓ x (⌊n i⌋₊:ℝ) ω).real
          (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) < c}) atTop (𝓝 0) := by
  classical
  dsimp only
  let ℓ := realPosition (step e)
  by_cases hex : ∃ r : ℕ → ℝ, IsGaussianSequence (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r
  · obtain ⟨r₀,hr₀⟩ := hex
    obtain ⟨W,hW,-⟩ := actual_quenched_gaussian_path_tests ν hue e f hef htrans r₀ hr₀ 2 (by norm_num)
    obtain ⟨δ,B,hδ,hB,F,hF,hFs,hb⟩ := brownian_positive_common_time_window W
      (2/(2*commonMeanWidth ν ℓ)) hW ⟨(1:ℝ)/2,by norm_num,by norm_num⟩ hρ
    refine ⟨(∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/4,by positivity,?_⟩
    intro r hr bStar hbStar x
    exact quenched_gaussian_success_tube_from_test ν hue e f hef htrans W hW ρ δ B hδ F hF hFs hb r hr bStar hbStar x
  · refine ⟨1,by norm_num,?_⟩
    intro r hr
    exact (hex ⟨r,hr⟩).elim

end DirectionalTransience

end

end

end OAI
