import Mathlib
import OAI.Probability.Ballisticity.Walk.SharedPairPathLimit
import OAI.Probability.Ballisticity.Coupling.QuenchedConcentration

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma pair_weak_test_moments {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (η : Measure (Ω × Ω)) [IsProbabilityMeasure η] (X : ℕ → Ω → E)
    (hX : ∀ i, Measurable (X i)) (W : ProbabilityMeasure E)
    (μ : ℕ → ProbabilityMeasure (E × E))
    (hμ : ∀ i, (μ i : Measure (E × E))=η.map (fun P => (X i P.1,X i P.2)))
    (hlim : Tendsto μ atTop (𝓝 (W.prod W))) (F : E →ᵇ ℝ) :
    Tendsto (fun i => ∫ P, F (X i P.1) ∂η) atTop (𝓝 (∫ z, F z ∂(W : Measure E))) ∧
    Tendsto (fun i => ∫ P, F (X i P.1)*F (X i P.2) ∂η) atTop
      (𝓝 ((∫ z, F z ∂(W : Measure E))^2)) := by
  let F1 : (E × E) →ᵇ ℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  let F2 : (E × E) →ᵇ ℝ := F.compContinuous ⟨Prod.snd,continuous_snd⟩
  have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F1
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (F1*F2)
  have hmap (i : ℕ) (G : (E × E) →ᵇ ℝ) :
      (∫ z, G z ∂(μ i : Measure (E × E)))=∫ P, G (X i P.1,X i P.2) ∂η := by
    rw [hμ i,integral_map (by fun_prop) G.continuous.aestronglyMeasurable]
  simp_rw [hmap] at hf hg
  have h1 : (∫ z, F1 z ∂(↑(W.prod W) : Measure (E × E)))=∫ z, F z ∂(W : Measure E) := by
    change (∫ z, F z.1 ∂(W : Measure E).prod (W : Measure E))=_
    rw [integral_fun_fst]
    simp
  have h2 : (∫ z, (F1*F2) z ∂(↑(W.prod W) : Measure (E × E)))=(∫ z, F z ∂(W : Measure E))^2 := by
    change (∫ z, F z.1*F z.2 ∂(W : Measure E).prod (W : Measure E))=_
    rw [integral_prod_mul,pow_two]
  rw [h1] at hf
  rw [h2] at hg
  exact ⟨hf,hg⟩

theorem actual_quenched_gaussian_path_tests {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (T : ℝ) (hT : 0 < T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x : Lattice d, ∀ F : C(unitInterval,ℝ) →ᵇ ℝ,
      let M := fun i => quenchedMedianPathTest ν ℓ hp f x (r i) (n i) T F
      let b := ∫ z, F z ∂(W : Measure C(unitInterval,ℝ))
      Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂noDropPairEnvironment ν ℓ x x) atTop (𝓝 0) ∧
      TendstoInMeasure (environmentLaw ν) M atTop (fun _ => b) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  obtain ⟨W,hW,hlim⟩ := shared_median_pair_path_limit ν hue e f hef htrans r hr T hT
  refine ⟨W,hW,?_⟩
  intro x F
  let η := sharedConditionedPairLaw ν ℓ x x
  have : IsProbabilityMeasure η := sharedConditionedPairLaw_probability ν ℓ x x
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x x))
  let X := fun i => medianFirstHitPath ν ℓ hp f x (r i) (n i) T
  have hX (i : ℕ) : Measurable (X i) := measurable_medianFirstHitPath _ _ _ _ _ _ _ _
  let μ : ℕ → ProbabilityMeasure RealPathPair := fun i => ⟨η.map (fun P => (X i P.1,X i P.2)),
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance⟩
  have hlim' : Tendsto μ atTop (𝓝 (W.prod W)) := hlim (fun _ => x) μ (fun _ => rfl)
  obtain ⟨hm1,hm2⟩ := pair_weak_test_moments η X hX W μ (fun _ => rfl) hlim' F
  exact actual_quenched_concentration_of_pair_moments ν hue ℓ (signed_direction_unit e) htrans x
    (fun i X' => F (X i X')) (fun i => F.continuous.measurable.comp (hX i)) ‖F‖ (norm_nonneg _)
    (fun i X' => F.norm_coe_le_norm _) _ hm1 hm2

end DirectionalTransience

end

end

end OAI
