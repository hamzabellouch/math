import OAI.Probability.InvariantIsing.Fields.SpinPriorContactMinimum
import OAI.Probability.InvariantIsing.Fields.PriorPerturbationCost
import OAI.Probability.InvariantIsing.Fields.PriorMinimumCoordinates

namespace OAI

/-! Uniform perturbation removal with the quenched cascade kept inside the logarithm. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorPerturbationPressureMean_prior_average
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    Integrable (fun T => priorPerturbationPressureMean μ (labeledSpinReference n π T)
      eig c I t h u v) (labeledCascadeLaw n b : Measure (LabeledTree n)) ∧
    spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v =
      ∫ T, priorPerturbationPressureMean μ (labeledSpinReference n π T) eig c I t h u v
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  obtain ⟨hi,he⟩ := spinPriorMeanPressure_prior_average (n := n) hhaar hgauss hN μ hμ π
    (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u) b
    (fun j : Fin N => enumeratedTreeDegree m j) h hh h0
  have hpoint T : priorNamespacedMeanPressure μ (labeledSpinReference n π T)
      (diagonalPerturbedEigenvalues eig I v t) c I
      (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
      (fun j : Fin N => enumeratedTreeDegree m j) h+h n/2 =
      priorPerturbationPressureMean μ (labeledSpinReference n π T) eig c I t h u v := by
    rw [priorPerturbationPressureMean_eq_namespaced]
    unfold priorNamespacedMeanPressure
    ring
  refine ⟨(hi.add (integrable_const (h n/2))).congr (ae_of_all _ hpoint),?_⟩
  unfold spinPriorPerturbationPressureMean
  rw [he]
  have he' := integral_add hi (integrable_const (h n/2))
  simp only [integral_const,probReal_univ,one_smul] at he'
  rw [← he']
  exact integral_congr_ae (ae_of_all _ hpoint)

lemma spinPriorPerturbationPressureMean_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2) :
    |spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v-
      spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h 0 0| ≤
      2*m*perturbationScale N+8*perturbationScale N^2 := by
  obtain ⟨hi,he⟩ := spinPriorPerturbationPressureMean_prior_average hhaar hgauss hN μ hμ π
    eig c I b t h hh h0 u v
  obtain ⟨hj,hf⟩ := spinPriorPerturbationPressureMean_prior_average hhaar hgauss hN μ hμ π
    eig c I b t h hh h0 0 0
  rw [he,hf,← integral_sub hi hj]
  have hn := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => priorPerturbationPressureMean μ (labeledSpinReference n π T) eig c I t h u v-
      priorPerturbationPressureMean μ (labeledSpinReference n π T) eig c I t h 0 0)
    (C := 2*m*perturbationScale N+8*perturbationScale N^2)
    (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs] using priorPerturbationPressureMean_cost hhaar hgauss hN
        μ hμ (labeledSpinReference n π T) eig c I t h hh h0 u hu v hv)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hn

lemma spinPriorContactPressure_temperature_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (s t : ℝ) :
    |spinPriorContactPressure μ π eig c I b (s,a,u,v)-
      spinPriorContactPressure μ π eig c I b (t,a,u,v)| ≤ (K/2)*|s-t| := by
  obtain ⟨hi,he⟩ := spinPriorContactPressure_prior_average hhaar hgauss hN μ hμ π eig c I b (s,a,u,v) ha
  obtain ⟨hj,hf⟩ := spinPriorContactPressure_prior_average hhaar hgauss hN μ hμ π eig c I b (t,a,u,v) ha
  rw [he,hf,← integral_sub hi hj]
  have hn := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => priorContactPressure μ (labeledSpinReference n π T) eig c I (s,a,u,v)-
      priorContactPressure μ (labeledSpinReference n π T) eig c I (t,a,u,v))
    (C := (K/2)*|s-t|)
    (ae_of_all _ fun T => by
      have ht := priorPerturbationPressureMean_temperature_modulus hhaar hgauss hN μ hμ
        (labeledSpinReference n π T) eig c I (finiteFieldPath a) (monotone_finiteFieldPath ha)
        (finiteFieldPath_nonneg ha 0) u v K hK s t
      simpa only [priorContactPressure, sub_sub_sub_cancel_right, Real.norm_eq_abs] using ht)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hn

end InvariantIsing

end

end OAI
