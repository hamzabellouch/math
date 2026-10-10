import OAI.Probability.InvariantIsing.Arrays.NSpinTensorComparison
import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights

namespace OAI

/-! The rotation modulus with the manuscript's actual finite perturbation amplitudes. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem abs_tensorPerturbationPressure_sub_rotation_le {N m : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1))
    (n : ℕ) (treeDegree : Fin N → ℕ) (h : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    let v := tensorPathProfile I degree n treeDegree h
    |tensorEnrichedPressure eig (specialRotation U) c I degree (tensorPerturbationAmplitude N u)
        n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig (specialRotation V) c I degree (tensorPerturbationAmplitude N u)
        n b (fun i => v (i + 1)) (v 0)| ≤
      (K + 8 * perturbationScale N ^ 2 * D) * frobeniusDistance U V := by
  intro v
  have hc := abs_tensorPathPressure_sub_rotation_le hN eig c U V K hK heig I degree
    (tensorPerturbationAmplitude N u) n treeDegree h b hb
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ (show 0 ≤ frobeniusDistance U V from Real.sqrt_nonneg _)
  have he := mul_le_mul_of_nonneg_left
    (tensorPerturbationAmplitude_degree_sum_le u hu degree D hD hdegree)
    (show 0 ≤ 2 * (N : ℝ)⁻¹ by positivity)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hid : 2 * (N : ℝ)⁻¹ * (4 * N * perturbationScale N ^ 2 * D) =
      8 * perturbationScale N ^ 2 * D := by field_simp; ring
  rw [hid] at he
  linarith

theorem abs_tensorPerturbationPressure_sub_rotation_uniform {N m : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1))
    (n : ℕ) (treeDegree : Fin N → ℕ) (h : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    let v := tensorPathProfile I degree n treeDegree h
    |tensorEnrichedPressure eig (specialRotation U) c I degree (tensorPerturbationAmplitude N u)
        n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig (specialRotation V) c I degree (tensorPerturbationAmplitude N u)
        n b (fun i => v (i + 1)) (v 0)| ≤ (K + 8 * D) * frobeniusDistance U V := by
  intro v
  have hc := abs_tensorPerturbationPressure_sub_rotation_le hN eig c U V K hK heig
    I degree u hu D hD hdegree n treeDegree h b hb
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ (show 0 ≤ frobeniusDistance U V from Real.sqrt_nonneg _)
  have hbnd := mul_le_mul_of_nonneg_right (perturbationScale_sq_le_one hN)
    (show 0 ≤ 8 * D by positivity)
  nlinarith

end InvariantIsing

end

end OAI
