import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusL2Product
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevConjugation

namespace OAI

/-! # Physical complex conjugation under the torus Fourier isometry -/

open MeasureTheory
open scoped ComplexConjugate

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure T)
noncomputable local instance torusConjugationMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusConjugationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def torusL2Conjugation : H →L[ℝ] H :=
  (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 volume

theorem torusL2Conjugation_ae (f : H) : torusL2Conjugation f =ᵐ[volume] (fun x => conj (f x)) :=
  ContinuousLinearMap.coeFn_compLpL _ f

theorem torusL2Conjugation_coefficient (f : H) (n : Fin 12 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Conjugation f) n =
      conj (UnitAddTorus.mFourierCoeff f (-n)) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [torusL2Conjugation_ae f] with x hx
  simp only [hx, neg_neg, smul_eq_mul, map_mul, UnitAddTorus.mFourier_neg]

theorem torusFourierIsometry_conjugate (f : FourierL2) :
    torusFourierIsometry (fourierConjugate f) = torusL2Conjugation (torusFourierIsometry f) := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext i
  obtain ⟨n, rfl⟩ := frequencyCoordinatesEquiv.surjective i
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr]
  change UnitAddTorus.mFourierCoeff (torusFourierIsometry (fourierConjugate f)) (frequencyCoordinates n) =
    UnitAddTorus.mFourierCoeff (torusL2Conjugation (torusFourierIsometry f)) (frequencyCoordinates n)
  rw [torusL2Conjugation_coefficient, torusFourierIsometry_coefficient]
  have hn : -frequencyCoordinates n = frequencyCoordinates (-n) := by
    exact (frequencyCoordinatesEquiv.map_neg n).symm
  rw [hn, torusFourierIsometry_coefficient, fourierConjugate_apply]

end DefocusingNLS

end OAI
