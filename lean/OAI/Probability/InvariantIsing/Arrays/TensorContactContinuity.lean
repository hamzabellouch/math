import OAI.Probability.InvariantIsing.Arrays.TensorContactRegion
import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureModulus
import OAI.Probability.InvariantIsing.Arrays.TensorFieldModulus

namespace OAI

/-! Joint continuity of the actual centered pressure in temperature, field
covariance increments and both complete perturbation amplitudes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)

private lemma centered_complete_amplitude_modulus (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u u' : Fin N → ℝ) (v v' : Fin m → ℝ) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) h -
      tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v' t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u')
        n b (fun j => enumeratedTreeDegree m j) h| ≤
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
        (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
        perturbationScale N * ∑ a, |v a - v' a| := by
  rw [tensorNamespacedMeanPressure_eq_perturbation μ eig c I u v t n b h hb,
    tensorNamespacedMeanPressure_eq_perturbation μ eig c I u' v' t n b h hb,
    sub_sub_sub_cancel_right]
  exact tensorPerturbationPressureMean_modulus hhaar hgauss hN μ hμ eig c I t n b hb h hh h0 u u' v v'

lemma tensorContactPressure_modulus (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (p q : TensorContactParameter N m n)
    (hp : ∀ j, 0 ≤ p.2.1 j) (hq : ∀ j, 0 ≤ q.2.1 j) :
    |tensorContactPressure μ eig c I b p - tensorContactPressure μ eig c I b q| ≤
      (K / 2) * |p.1 - q.1| + (∑ j, |p.2.1 j - q.2.1 j|) / 2 +
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
        (tensorPerturbationAmplitude N p.2.2.1) (tensorPerturbationAmplitude N q.2.2.1) +
      perturbationScale N * ∑ a, |p.2.2.2 a - q.2.2.2 a| := by
  let F := fun (t : ℝ) (a : Fin (n + 1) → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) =>
    tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath a)
  have ht := tensorNamespacedMeanPressure_temperature_modulus (by omega) μ eig c I p.2.2.2
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
    (monotone_finiteFieldPath hp) (finiteFieldPath_nonneg hp 0) K hK p.1 q.1
  have ha := tensorNamespacedMeanPressure_field_modulus (by omega) μ
    (diagonalPerturbedEigenvalues eig I p.2.2.2 q.1) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) p.2.1 q.2.1 hp hq
  have hu := centered_complete_amplitude_modulus hhaar hgauss hN μ hμ eig c I q.1 n b hb
    (finiteFieldPath q.2.1) (monotone_finiteFieldPath hq) (finiteFieldPath_nonneg hq 0)
    p.2.2.1 q.2.2.1 p.2.2.2 q.2.2.2
  have h1 := abs_sub_le (F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (F q.1 p.2.1 p.2.2.1 p.2.2.2) (F q.1 q.2.1 p.2.2.1 p.2.2.2)
  have h2 := abs_sub_le (F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (F q.1 q.2.1 p.2.2.1 p.2.2.2) (F q.1 q.2.1 q.2.2.1 q.2.2.2)
  change |F p.1 p.2.1 p.2.2.1 p.2.2.2 - F q.1 q.2.1 q.2.2.1 q.2.2.2| ≤ _
  linarith

theorem continuousOn_tensorContactPressure (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) {s : Set (TensorContactParameter N m n)}
    (hs : ∀ p ∈ s, ∀ j, 0 ≤ p.2.1 j) :
    ContinuousOn (tensorContactPressure μ eig c I b) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let E := fun p : s => (K / 2) * |p.val.1 - q.val.1| +
    (∑ j, |p.val.2.1 j - q.val.2.1 j|) / 2 +
    2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
      (tensorPerturbationAmplitude N p.val.2.2.1) (tensorPerturbationAmplitude N q.val.2.2.1) +
    perturbationScale N * ∑ a, |p.val.2.2.2 a - q.val.2.2.2 a|
  have hE : Continuous E := by
    unfold E tensorAmplitudeModulus tensorPerturbationAmplitude
    fun_prop
  have hEq : E q = 0 := by simp [E, tensorAmplitudeModulus]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, domRestrict_apply, E] using
        tensorContactPressure_modulus hhaar hgauss hN μ hμ eig c I b hb K hK p.val q.val
          (hs p.val p.property) (hs q.val q.property))
  simpa only [hEq] using hE.tendsto q

end InvariantIsing

end

end OAI
