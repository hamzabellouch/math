import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Leaf exhaustion for bounded replica observables of an arbitrary
integrable Gibbs Hamiltonian. No Gaussian insertion remains in the Ward
terms to which this lemma will be applied. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma normalizedRestriction_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set X) (T : Set Y) :
    (normalizedRestriction μ S).prod (normalizedRestriction ν T) =
      normalizedRestriction (μ.prod ν) (S ×ˢ T) := by
  unfold normalizedRestriction
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
    Measure.prod_prod, ENNReal.mul_inv]
  · exact Or.inr (measure_ne_top ν T)
  · exact Or.inl (measure_ne_top μ S)

lemma referenceReplicaMean_restriction_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ}
    (D : (Fin r → X) → ℝ) {B : ℝ} (hD : ∀ σ, |D σ| ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => referenceReplicaMean (normalizedRestriction ν (S n)) H D) atTop
      (𝓝 (referenceReplicaMean ν H D)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (S n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ : Fin r => ν)) := by
    simpa only [Real.exp_sum] using
      (Integrable.fintype_prod (fun _ : Fin r => hH))
  have hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)) * D σ)
      (Measure.pi (fun _ : Fin r => ν)) :=
    he.mul_bdd (measurable_of_countable D).aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hD σ)
  have hz : (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) ≠ 0 := by
    rw [reference_replica_partition]
    exact pow_ne_zero _ (integral_exp_pos hH).ne'
  have ht := normalized_restriction_gibbs_tendsto
    (fun n => MeasurableSet.univ_pi (fun _ : Fin r => hS n))
    (replica_restriction_eventually hexh) he hi hz
  simpa only [referenceReplicaMean_eq_ratio,
    ← normalizedRestriction_pi (fun _ : Fin r => S _) (fun _ => hpos _)] using ht

theorem expected_referenceReplicaMean_restriction_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    {r : ℕ} (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z, |D z| ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ ω, referenceReplicaMean (normalizedRestriction ν (S n))
      (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) atTop
      (𝓝 (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (S n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    exact (measurable_random_referenceReplicaMean
      (ν := fun _ : Ω => normalizedRestriction ν (S n)) measurable_const hH hD).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact referenceReplicaMean_abs_le _ _ _
        (hD.comp (measurable_const.prodMk measurable_id)) hB (fun σ => hbound (ω,σ))
  · filter_upwards [he] with ω hω
    exact referenceReplicaMean_restriction_tendsto ν (fun x => H (ω,x)) hω
      (fun σ => D (ω,σ)) (fun σ => hbound (ω,σ)) hS hexh hpos

end InvariantIsing

end

end OAI
