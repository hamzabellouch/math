import OAI.Probability.InvariantIsing.Fields.SpinPriorPerturbationCost
import OAI.Probability.InvariantIsing.Fields.PriorZeroFieldPressure

namespace OAI

/-! With no Gaussian field or perturbation, the arbitrary-depth quenched
cascade disappears and leaves the original physical constrained pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma finiteLogIntegral_labeledSpinReference {N n : ℕ}
    (π : Measure (Spin N)) (T : LabeledTree n) (H : Spin N → ℝ) :
    finiteLogIntegral (labeledSpinReference n π T) (fun x => H x.1)=finiteLogIntegral π H := by
  unfold finiteLogIntegral labeledSpinReference
  congr 1
  simpa only [probReal_univ,one_smul] using integral_fun_fst
    (μ := π) (ν := labeledLeafLaw n T) (fun σ => Real.exp (H σ))

lemma spinPrior_unperturbed_pressure (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (t : ℝ) :
    spinPriorPerturbationPressureMean (n := n) μ π eig c I b t (fun _ => 0) 0 0 =
      priorPerturbationPressureMean μ (labeledSpinReference 0 π PUnit.unit)
        eig c I t (fun _ => 0) 0 0 := by
  have he := (spinPriorPerturbationPressureMean_prior_average (n := n) hhaar hgauss hN μ hμ
    π eig c I b t (fun _ => 0) (fun _ _ _ => le_rfl) le_rfl 0 0).2
  rw [he]
  have hpoint (T : LabeledTree n) :
      priorPerturbationPressureMean μ (labeledSpinReference n π T) eig c I t (fun _ => 0) 0 0 =
      priorPerturbationPressureMean μ (labeledSpinReference 0 π PUnit.unit) eig c I t (fun _ => 0) 0 0 := by
    rw [prior_zero_field_pressure,prior_zero_field_pressure]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with U
    exact (finiteLogIntegral_labeledSpinReference π T
      (fun σ => rotatedEnergy (fun i => t*eig i) (specialRotation U) σ+fieldEnergy c σ)).trans
      (finiteLogIntegral_labeledSpinReference (n := 0) π (PUnit.unit : LabeledTree 0)
        (fun σ => rotatedEnergy (fun i => t*eig i) (specialRotation U) σ+fieldEnergy c σ)).symm
  simp_rw [hpoint]
  simp

lemma spinPrior_restricted_unperturbed_pressure (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (t : ℝ) :
    spinPriorPerturbationPressureMean (n := n) μ (restrictedSpinPrior C hC : Measure (Spin N))
        eig c I b t (fun _ => 0) 0 0 =
      (∫ U, restrictedRotatedPressure C (fun i => t*eig i) (specialRotation U) c ∂μ)-
        (N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2) := by
  rw [spinPrior_unperturbed_pressure hhaar hgauss hN μ hμ]
  exact restricted_zero_field_pressure μ C hC eig c I t

end InvariantIsing

end

end OAI
