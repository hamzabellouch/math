import OAI.GroupTheory.PolycyclicRecognition.Algebra.DifferenceAmplitudeWord
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingPolynomialCoordinates

namespace OAI

/-! # Fixed source bundles in joint independent coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

abbrev WordLawData (I : Type*) (n : ℕ) :=
  ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)

def bundleWordEndpoint {I : Type*} {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : WordLawData I n) (t : Fin M → ℝ) : Fin N → ℝ :=
  output.symm (fun j => differenceAmplitudeWordEndpoint a letters p (input t j))

theorem hasPolynomialCoordinates_linear_pi_output {P : Type*} {h n m k : ℕ}
    (T : (Fin h → Fin n → ℝ) →L[ℝ] (Fin k → ℝ))
    (f : P → (Fin m → ℝ) → Fin h → Fin n → ℝ)
    (hf : ∀ i j, HasPolynomialFormula (fun p x => f p x i j)) :
    HasPolynomialCoordinates (fun p x => T (f p x)) := by
  have he (v : Fin h → Fin n → ℝ) :
      v = ∑ i : Fin h, ∑ j : Fin n, v i j • Pi.single i (Pi.single j 1) := by
    funext i j
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  intro k
  have he' : (fun p x => T (f p x) k) = (fun p x =>
      ∑ i : Fin h, ∑ j : Fin n, f p x i j * T (Pi.single i (Pi.single j 1)) k) := by
    funext p x
    conv_lhs => rw [he (f p x)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he']
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact (hf i j).mul (hasPolynomialFormula_const (fun _ => T (Pi.single i (Pi.single j 1)) k))

theorem hasPolynomialCoordinates_bundleWordEndpoint {I : Type*} {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    HasPolynomialCoordinates (bundleWordEndpoint (n := n) a letters input output) := by
  apply hasPolynomialCoordinates_linear_pi_output output.symm.toContinuousLinearMap
  intro i
  have ht := hasPolynomialCoordinates_linear (fun _ : WordLawData I n =>
    (differenceParameters m).comp ((ContinuousLinearMap.proj i).comp input.toContinuousLinearMap))
  have hf : HasPolynomialCoordinates (fun p : WordLawData I n => fun t : Fin M → ℝ =>
      differenceAmplitudeWordEndpoint a letters p (input t i)) := by
    unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
    apply hasPolynomialCoordinates_listProduct a Prod.fst
    intro j
    exact (hasPolynomialCoordinates_const (fun p : WordLawData I n => p.2 (letters j))).smul (ht j)
  exact hf

theorem contDiff_bundleWordEndpoint {I : Type*} [Fintype I] {n m h c M N : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    ContDiff ℝ q (fun z : WordLawData I n × (Fin M → ℝ) =>
      bundleWordEndpoint a letters input output z.1 z.2) := by
  unfold bundleWordEndpoint differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  apply output.symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  apply contDiff_polynomialListProduct_ofFn a
    (fun z : WordLawData I n × (Fin M → ℝ) => z.1.1) _ contDiff_fst.fst
  intro k
  have ht : ContDiff ℝ q (fun z : WordLawData I n × (Fin M → ℝ) =>
      differenceParameters m (input z.2 j) k) :=
    (contDiff_apply ℝ ℝ k).comp ((differenceParameters m).contDiff.comp
      ((contDiff_apply ℝ (Fin (m + m) → ℝ) j).comp (input.contDiff.comp contDiff_snd)))
  exact ht.smul ((contDiff_apply ℝ (Fin n → ℝ) (letters k)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
