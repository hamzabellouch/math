import OAI.Probability.InvariantIsing.Cavity.CavityHaarMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityWeakRadialCutoff

namespace OAI

/-! Weak convergence of the actual Haar cavity marks. In particular it
applies to bounded replica tests with a hard spatial cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavityHaarMarkedLaw_tendsto {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (K : Set L) (hK : IsCompact K)
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (l : (k : ℕ) → X k → L) (hlM : ∀ k, Measurable (l k))
    (hl : ∀ k x, l k x ∈ K)
    (v : (k : ℕ) → X k → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x a i j, |cavityGroupReplicaGram (v k x) a i j| ≤ C)
    (Q : ℕ → ProbabilityMeasure
      (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ))
    (Q₀ : ProbabilityMeasure
      (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ))
    (hQ : ∀ k, (Q k : Measure _) = (P k).map
      (fun x => (l k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hQ₀ : ∀ᵐ p ∂(Q₀ : Measure
      (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)), p.2.PosSemidef) :
    Tendsto (fun k => cavityHaarMarkedLaw (P k) (μ k) (l k) (hlM k) (v k) (hvM k) (A₀ k))
      atTop (𝓝 (cavityGaussianMarkedLaw Q₀)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x),
    cavityGaussianMarkedLaw_integral _ _ F.continuous.measurable
      (fun x => F.norm_coe_le_norm x)]
  exact cavityGroupHaarFrame_joint_law_tendsto K hK N hN μ A₀ hA₀ X P l hlM hl
    v hvM C hv Q Q₀ hQ hlim hQ₀ F

theorem cavityGaussianMarkedLaw_radial_cutoff_tendsto
    {a L : Type*} [Fintype a] [DecidableEq a]
    [MetricSpace L] [MeasurableSpace L] [BorelSpace L] [SecondCountableTopology L]
    (Q : ℕ → ProbabilityMeasure (L × Matrix a a ℝ))
    (Q₀ : ProbabilityMeasure (L × Matrix a a ℝ))
    (hQ : Tendsto Q atTop (𝓝 Q₀))
    (hS : ∀ n, ∀ᵐ p ∂(Q n : Measure (L × Matrix a a ℝ)), p.2.PosSemidef)
    (hS₀ : ∀ᵐ p ∂(Q₀ : Measure (L × Matrix a a ℝ)), p.2.PosSemidef)
    (R : L × EuclideanSpace ℝ a → ℝ) (hR : Continuous R)
    (F : L × EuclideanSpace ℝ a →ᵇ ℝ) (B : ℝ)
    (hnull : (cavityGaussianMarkedLaw Q₀ : Measure (L × EuclideanSpace ℝ a))
      {x | R x = B} = 0) :
    Tendsto (fun n => ∫ x, {x | R x ≤ B}.indicator (fun x => F x) x
        ∂(cavityGaussianMarkedLaw (Q n) : Measure (L × EuclideanSpace ℝ a)))
      atTop (𝓝 (∫ x, {x | R x ≤ B}.indicator (fun x => F x) x
        ∂(cavityGaussianMarkedLaw Q₀ : Measure (L × EuclideanSpace ℝ a)))) :=
  cavity_weak_radial_cutoff_integral _ _
    (cavityGaussianMarkedLaw_tendsto Q Q₀ hQ hS hS₀) R hR F B hnull

end InvariantIsing

end

end OAI
