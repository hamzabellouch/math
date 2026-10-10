import OAI.Probability.InvariantIsing.Fields.PriorMinimumEnvelope
import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPressure

namespace OAI

/-! The perturbation cost is uniform over all probability priors, including
product constraints whose masses can vanish exponentially in the dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorPerturbationPressureMean_cost (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2) :
    |priorPerturbationPressureMean μ ν eig c I t h u v -
      priorPerturbationPressureMean μ ν eig c I t h 0 0| ≤
        2*m*perturbationScale N + 8*perturbationScale N^2 := by
  have hc := priorPerturbationPressureMean_modulus hhaar hgauss hN μ hμ ν eig c I t h hh h0 u 0 v 0
  have he : tensorAmplitudeModulus (tensorPerturbationAmplitude N u)
      (tensorPerturbationAmplitude N 0) = ∑ j, (tensorPerturbationAmplitude N u j)^2 := by
    simp [tensorAmplitudeModulus, tensorPerturbationAmplitude, ← pow_two, mul_pow]
  rw [he] at hc
  have hs : (∑ a : Fin m, |v a - (0 : Fin m → ℝ) a|) ≤ 2*m := by
    calc
      _ ≤ ∑ _a : Fin m, (2 : ℝ) := Finset.sum_le_sum fun a _ => by simpa using hv a
      _ = _ := by simp; ring
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left (tensorPerturbationAmplitude_square_sum_le N u hu)
      (show 0 ≤ 2*(N : ℝ)⁻¹ by positivity))
    (mul_le_mul_of_nonneg_left hs (show 0 ≤ perturbationScale N from Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply hc.trans
  apply hb.trans_eq
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

lemma prior_minimum_perturbation_cost (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ ν eig c I t h u v ≤
        priorPerturbationObjective μ ν eig c I t h u' v') :
    |(-priorPerturbationObjective μ ν eig c I t h u v) -
      priorPerturbationPressureMean μ ν eig c I t h 0 0| ≤
        2*m*perturbationScale N + 8*perturbationScale N^2 ∧
      tensorMinimumPenalty u v ≤ 2*(2*m*perturbationScale N + 8*perturbationScale N^2) := by
  exact prior_minimum_envelope_cost μ ν eig c I t h u v hu hv hmin _ _
    (fun u' v' hu' hv' => priorPerturbationPressureMean_cost hhaar hgauss hN μ hμ ν eig c I t h hh h0
      u' (fun j => abs_le.mpr ⟨by linarith [(hu' j).1], (hu' j).2⟩)
      v' (fun a => abs_le.mpr ⟨by linarith [(hv' a).1], (hv' a).2⟩))

end InvariantIsing

end

end OAI
