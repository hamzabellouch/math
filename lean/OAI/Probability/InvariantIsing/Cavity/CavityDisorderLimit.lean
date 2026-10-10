import OAI.Probability.InvariantIsing.Cavity.CavityDisorderTestComparison

namespace OAI

/-! The actual finite perturbation comparison vanishes on every fixed
geometric cutoff, also after averaging over a varying disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavityCylinderReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A : X → ℕ →₀ ℝ) {r : ℕ} (F : (Fin r → X) → ℝ)
    (hmF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ, |F σ| ≤ B) :
    |cavityCylinderReplicaMean ν H A F| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
    (f := fun g => referenceReplicaMean ν
      (fun x => H x + cylinderField (A x) g) F)
    (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs]
      exact referenceReplicaMean_abs_le ν _ F hmF hB hF)
  simpa only [cavityCylinderReplicaMean, Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem cavity_disorder_cutoff_difference_tendsto
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    {n m depth r : ℕ}
    (U : (k : ℕ) → Ω k → Rotation (N k + n))
    (V : (k : ℕ) → Ω k → Rotation (N k))
    (I : (k : ℕ) → Fin m → Finset (Fin (N k + n)))
    (J : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (eig : (k : ℕ) → Fin (N k + n) → ℝ) (eig₀ : (k : ℕ) → Fin (N k) → ℝ)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2) (t : ℝ)
    (w : (k : ℕ) → Ω k → Spin (N k) × Spin n → ℝ)
    (hw : ∀ k ω x, 1 ≤ w k ω x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (herr : ∀ k ω x y a,
      |projectedOverlap (U k ω) (I k a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
        projectedOverlap (V k ω) (J k a) x.1 y.1| ≤
          C / N k * (w k ω x + w k ω y))
    (ν : (k : ℕ) → (ω : Ω k) →
      Measure {x : (Spin (N k) × Spin n) × LabeledLeaf depth // w k ω x.1 ≤ D})
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (Φ : (k : ℕ) → (ω : Ω k) →
      (Fin r → {x : (Spin (N k) × Spin n) × LabeledLeaf depth // w k ω x.1 ≤ D}) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hΦ : ∀ k ω σ, |Φ k ω σ| ≤ B) :
    Tendsto (fun k => ∫ ω,
      cavityBaseCutoffReplicaMean (U k ω) (V k ω) (J k) (eig k) (eig₀ k)
        (v k) (u k) t (w k ω) D (ν k ω) (Φ k ω) -
      cavityFullCutoffReplicaMean (U k ω) (I k) (eig k) (v k) (u k) t
        (w k ω) D (ν k ω) (Φ k ω) ∂P k) atTop (𝓝 0) := by
  let K := fun k => cavityCovarianceRate n C (N k) * (2 * D)
  let E := fun k => cavityDeterministicRate n m (2 * C) (N k) * D
  have hK : Tendsto K atTop (𝓝 0) := by
    simpa only [K, Function.comp_def, zero_mul] using
      ((cavityCovarianceRate_tendsto n C).comp hNlim).mul_const (2 * D)
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, Function.comp_def, zero_mul] using
      ((cavityDeterministicRate_tendsto n m (2 * C)).comp hNlim).mul_const D
  apply cavity_secant_error_tendsto (C := B ^ 2 / 2) (by positivity)
    (δ := fun k => 2 * (r : ℝ)^2 * K k + 2 * r * K k + 2 * r * E k)
  · simpa only [mul_zero, add_zero] using
      ((hK.const_mul (2 * (r : ℝ)^2)).add (hK.const_mul (2 * (r : ℝ)))).add
        (hE.const_mul (2 * (r : ℝ)))
  · intro s hs
    exact Eventually.of_forall fun k => by
      simpa only [K, E, div_mul_eq_mul_div] using
        cavity_disorder_cutoff_test_comparison (P k) (hN k) (U k) (V k) (I k) (J k)
          (eig k) (eig₀ k) (v k) (hv k) (u k) (hu k) t (w k) (hw k)
          hC hD (herr k) (ν k) (Φ k) hB (hΦ k) hs

end InvariantIsing

end

end OAI
