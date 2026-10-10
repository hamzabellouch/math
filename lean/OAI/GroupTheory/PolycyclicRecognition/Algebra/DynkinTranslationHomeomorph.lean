import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinFiniteDifference
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormedLiePolynomial

namespace OAI

/-! # Polynomial homeomorphisms given by BCH translation

Both translations have explicit finite correction inverses. The inverses
also depend continuously on the translating vector.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {c d : ℕ} (coeff : DynkinCoefficients c 2)
  (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
  (hd : lowerCentralSeries ℝ L L d = ⊥)

theorem continuous_binaryDynkin :
    Continuous (fun p : L × L => finiteDynkinPolynomial coeff ![p.1, p.2]) := by
  apply (contDiff_normed_finiteDynkinPolynomial (r := ∞) coeff _ ?_).continuous
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd

def leftDynkinTranslationHomeomorph (a : L) : L ≃ₜ L :=
  homeomorphOfRaisesDifferenceFiltration
    (fun k => (lowerCentralSeries ℝ L L k).toSubmodule) (by simp)
    (congrArg LieSubmodule.toSubmodule hd)
    (fun x => finiteDynkinPolynomial coeff ![a, x])
    ((continuous_binaryDynkin coeff).comp (continuous_const.prodMk continuous_id))
    (binaryDynkin_raises_difference coeff haxis a)

def rightDynkinTranslationHomeomorph (a : L) : L ≃ₜ L :=
  homeomorphOfRaisesDifferenceFiltration
    (fun k => (lowerCentralSeries ℝ L L k).toSubmodule) (by simp)
    (congrArg LieSubmodule.toSubmodule hd)
    (fun x => finiteDynkinPolynomial coeff ![x, a])
    ((continuous_binaryDynkin coeff).comp (continuous_id.prodMk continuous_const))
    (binaryDynkin_raises_left_difference coeff haxis a)

theorem continuous_rightDynkinTranslationInverse :
    Continuous (fun p : L × L => (rightDynkinTranslationHomeomorph coeff haxis hd p.1).symm p.2) := by
  change Continuous (fun p : L × L => filteredNewton
    (fun x => finiteDynkinPolynomial coeff ![x, p.1]) p.2 d)
  exact continuous_parametric_filteredNewton
    (fun a x => finiteDynkinPolynomial coeff ![x, a])
    ((continuous_binaryDynkin coeff).comp (continuous_snd.prodMk continuous_fst)) d

theorem continuous_leftDynkinTranslationInverse :
    Continuous (fun p : L × L => (leftDynkinTranslationHomeomorph coeff haxis hd p.1).symm p.2) := by
  change Continuous (fun p : L × L => filteredNewton
    (fun x => finiteDynkinPolynomial coeff ![p.1, x]) p.2 d)
  exact continuous_parametric_filteredNewton
    (fun a x => finiteDynkinPolynomial coeff ![a, x]) (continuous_binaryDynkin coeff) d

end PolycyclicRecognition

end

end OAI
