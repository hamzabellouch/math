import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadeAverage
import OAI.Probability.InvariantIsing.Fields.PriorContactField
import OAI.Probability.InvariantIsing.Core.ContactModulus

namespace OAI

/-! Joint continuity for the actual cascade-enriched spin-prior contact
pressure, with the quenched cascade retained in the pressure integral. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (p : TensorContactParameter N m n) : ℝ :=
  spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    b (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)

lemma spinPriorContactPressure_prior_average
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (p : TensorContactParameter N m n) (hp : ∀ i, 0 ≤ p.2.1 i) :
    Integrable (fun T => priorContactPressure μ (labeledSpinReference n π T) eig c I p)
      (labeledCascadeLaw n b : Measure (LabeledTree n)) ∧
    spinPriorContactPressure μ π eig c I b p =
      ∫ T, priorContactPressure μ (labeledSpinReference n π T) eig c I p
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have h := spinPriorMeanPressure_prior_average (n := n) hhaar hgauss hN μ hμ π
    (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    b (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
    (monotone_finiteFieldPath hp) (finiteFieldPath_nonneg hp 0)
  simpa only [spinPriorContactPressure,priorContactPressure_eq_namespaced] using h

lemma spinPriorContactPressure_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (p q : TensorContactParameter N m n)
    (hp : ∀ i, 0 ≤ p.2.1 i) (hq : ∀ i, 0 ≤ q.2.1 i) :
    |spinPriorContactPressure μ π eig c I b p-spinPriorContactPressure μ π eig c I b q| ≤
      contactModulus K p q := by
  obtain ⟨hi,he⟩ := spinPriorContactPressure_prior_average hhaar hgauss hN μ hμ π eig c I b p hp
  obtain ⟨hj,hf⟩ := spinPriorContactPressure_prior_average hhaar hgauss hN μ hμ π eig c I b q hq
  rw [he,hf,← integral_sub hi hj]
  have hn := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => priorContactPressure μ (labeledSpinReference n π T) eig c I p-
      priorContactPressure μ (labeledSpinReference n π T) eig c I q)
    (C := contactModulus K p q)
    (ae_of_all _ fun T => by
      have hb := priorContactPressure_modulus hhaar hgauss hN μ hμ (labeledSpinReference n π T)
        eig c I K hK p q hp hq
      simpa only [Real.norm_eq_abs] using hb)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hn

theorem continuousOn_spinPriorContactPressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) {S : Set (TensorContactParameter N m n)}
    (hS : ∀ p ∈ S, ∀ i, 0 ≤ p.2.1 i) :
    ContinuousOn (spinPriorContactPressure μ π eig c I b) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hD : Continuous (fun p : S => contactModulus K p.val q.val) :=
    (continuous_contactModulus K q.val).comp continuous_subtype_val
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs,domRestrict_apply] using
        spinPriorContactPressure_modulus hhaar hgauss hN μ hμ π eig c I b K hK p.val q.val
          (hS p.val p.property) (hS q.val q.property))
  simpa only [contactModulus_self] using hD.tendsto q

end InvariantIsing

end

end OAI
