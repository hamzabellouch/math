import OAI.Probability.InvariantIsing.Arrays.TensorContactField
import OAI.Probability.InvariantIsing.Spectral.SpectralTemperatureFunctional

namespace OAI

/-! The temperature-coordinate inequality at an actual joint minimum.
The left variation remains valid at the upper endpoint t=1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_minimum_temperature {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q)
    (ht : 0 < p.1) (K : ℝ) (hK : ∀ i, |eig i| ≤ K)
    {V' : ℝ} (hV : HasDerivAt V V' p.1) :
    V' ≤ tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
      c I (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
      n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
      (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1) := by
  obtain ⟨hpt, ha, hsum, hu, hv⟩ := tensorContactRegion_bounds hp
  let M := fun t => tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I p.2.2.2 t)
    c I (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
  let E := tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
    c I (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
    (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)
  have hdM : HasDerivAt M E p.1 :=
    hasDerivAt_tensorNamespacedMeanPressure_temperature hN μ eig c I p.2.2.2
      (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
      n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
      (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) K hK p.1
  let F := fun t => -M t + V t
  have hdF : HasDerivAt F (-E + V') (p.1 - id 0) := by
    convert! hdM.fun_neg.fun_add hV using 1
    simp only [id_eq, sub_zero]
  have hd := hdF.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub p.1)
  simp only [mul_neg_one] at hd
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < p.1 :=
    (show ∀ᶠ a in 𝓝 (0 : ℝ), a < p.1 from Iio_mem_nhds ht).filter_mono nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hd.hasDerivWithinAt (by
    filter_upwards [hsmall, self_mem_nhdsWithin] with a hal ha0
    have hnew : (p.1 - a, p.2.1, p.2.2.1, p.2.2.2) ∈ tensorContactRegion N m n H :=
      tensorContactRegion_mem ⟨sub_nonneg.mpr hal.le, (sub_le_self _ ha0.le).trans hpt.2⟩
        ha hsum hu hv
    have hm := hmin _ hnew
    simp only [tensorContactObjective, tensorContactPressure] at hm
    change F (p.1 - 0) ≤ F (p.1 - a)
    rw [sub_zero]
    dsimp only [F, M]
    linarith)
  change V' ≤ E
  linarith


/-- The manuscript's strict temperature tilt gives an energy gap at the
same finite-volume minimum, including at temperature one. -/
theorem tensorContact_minimum_energy_gap {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (trial : OverlapPath) (δ S H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ) p ≤
      tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ) q)
    (ht : 0 < p.1) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    finiteInteractionEnergy ρ lam hρ hρsum p.1 trial + δ ≤
      tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
        c I (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1) := by
  apply tensorContact_minimum_temperature hN μ eig c I b w S
    (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ)
    H p hp hmin ht K hK
  convert! (hasDerivAt_finiteTemperatureFunctional ρ lam hρ hρsum trial p.1).fun_add
    ((hasDerivAt_id p.1).mul_const δ) using 1
  simp only [one_mul]

end InvariantIsing

end

end OAI
