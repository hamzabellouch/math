import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationBaseComparison
import OAI.Probability.InvariantIsing.Arrays.TensorZeroAmplitude
import OAI.Probability.InvariantIsing.Arrays.TensorContactStep
import OAI.Probability.InvariantIsing.Arrays.TensorContactBoundary

namespace OAI

/-! The genuine zero-temperature boundary differs from the entropy contact
bound only by the already controlled finite perturbation cost. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContact_zero_temperature_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (S : ℝ) (hS : entropyFunctional trial ≤ (S : EReal))
    (V : ℝ → ℝ) (hV : V 0 = 0) :
    -(2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) ≤
      tensorContactObjective μ eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (0, a, u, v) := by
  let step := contactFieldStep cut hc hfirst hlast a ha
  have hb : CascadeExponents n (chainExponent cut) :=
    chainExponent_admissible hc hfirst hlast
  have hP := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ
    eig (fun _ => 0) I u hu v hv 0 n (chainExponent cut) (finiteFieldPath a) hb
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => (0 : ℝ) * eig i) (specialRotation U) (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n (chainExponent cut)
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath a) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath a) 0) =
      fieldValue step 0 + finiteFieldPath a n / 2 := by
    have he := tensorPathPressure_field_zero_time (by omega : 0 < N) (specialRotation U) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (fun j => enumeratedTreeDegree m j) step
    have hs : heightSequence step = finiteFieldPath a :=
      heightSequence_contactFieldStep cut hc hfirst hlast a ha
    rw [hs] at he
    change _ - finiteFieldPath a n / 2 = fieldValue step 0 at he
    convert (sub_eq_iff_eq_add).mp he using 1
    simp only [zero_mul]
    rfl
  simp_rw [hbase] at hP
  simp only [integral_const, probReal_univ, one_smul, add_sub_cancel_right] at hP
  have hSreal : fieldValue step 0 + fieldPairing trial step / 2 ≤ S := by
    have he : ((fieldValue step 0 + fieldPairing trial step / 2 : ℝ) : EReal) ≤ (S : EReal) :=
      (le_iSup (fun h : FieldStep => ((fieldValue h 0 + fieldPairing trial h / 2 : ℝ) : EReal))
        step).trans hS
    exact_mod_cast he
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast a ha values hvalues
  change fieldPairing trial step = _ at hpair
  rw [hpair] at hSreal
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  have hW : 0 ≤ ∑ j : Fin m, (v j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  simp only [tensorContactObjective, tensorContactPressure, hV]
  have hp := (le_abs_self _).trans hP
  linarith

end InvariantIsing

end

end OAI
