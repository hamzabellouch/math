import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialEndpointCoordinates

namespace OAI

/-! # Independently varying every amplitude in a fixed generator word -/

noncomputable section

namespace PolycyclicRecognition

def amplitudeWordEndpoint {I : Type*} {n m c : ℕ} (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t : Fin m → ℝ) : Fin n → ℝ :=
  polynomialListProduct (dynkinProduct a p.1) (List.ofFn (fun j => t j • p.2 (letters j)))

theorem hasPolynomialCoordinates_amplitudeWordEndpoint {I : Type*} {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) :
    HasPolynomialCoordinates (amplitudeWordEndpoint (n := n) a letters) := by
  apply hasPolynomialCoordinates_listProduct a Prod.fst
  intro j
  apply HasPolynomialCoordinates.smul
  · exact hasPolynomialCoordinates_const (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ) =>
      p.2 (letters j))
  · exact hasPolynomialFormula_coordinate j

theorem contDiff_amplitudeWordEndpoint {I : Type*} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) {q : ℕ∞} :
    ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin m → ℝ) => amplitudeWordEndpoint (n := n) a letters z.1 z.2) := by
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).smul
      ((contDiff_apply ℝ (Fin n → ℝ) (letters j)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
