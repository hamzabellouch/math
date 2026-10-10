import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusL2Product
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierConvolution

namespace OAI

/-! # Fourier translation is multiplication by the physical character -/

open MeasureTheory
open scoped ENNReal

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance torusFourierTranslationMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusFourierTranslationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusFourierIsometry_single (n : frequencyLattice) :
    torusFourierIsometry (lp.single 2 n (1 : ℂ)) =
      UnitAddTorus.mFourierLp 2 (frequencyCoordinates n) := by
  exact (torusLatticeBasis.repr_symm_single n).trans (torusLatticeBasis_apply n)

theorem fourierTranslation_single (m n : frequencyLattice) :
    fourierTranslation m (lp.single 2 n (1 : ℂ)) = lp.single 2 (n + m) (1 : ℂ) := by
  classical
  ext l
  simp only [fourierTranslation_apply, lp.single_apply, Pi.single_apply]
  congr 1
  exact propext sub_eq_iff_eq_add

theorem torusFourierIsometry_translation (m : frequencyLattice) (f : FourierL2) :
    torusFourierIsometry (fourierTranslation m f) =
      torusL2Product (UnitAddTorus.mFourier (frequencyCoordinates m)) (torusFourierIsometry f) := by
  let I := torusFourierIsometry.toContinuousLinearEquiv.toContinuousLinearMap
  let A := I.comp (fourierTranslation m).toContinuousLinearMap
  let B := (torusL2Product (UnitAddTorus.mFourier (frequencyCoordinates m))).comp I
  have hsingle (n : frequencyLattice) : A (lp.single 2 n (1 : ℂ)) = B (lp.single 2 n (1 : ℂ)) := by
    change torusFourierIsometry (fourierTranslation m (lp.single 2 n (1 : ℂ))) =
      torusL2Product _ (torusFourierIsometry (lp.single 2 n (1 : ℂ)))
    rw [fourierTranslation_single, torusFourierIsometry_single,
      torusFourierIsometry_single, torusL2Product_mFourier]
    congr 2
    change frequencyCoordinatesEquiv (n + m) = frequencyCoordinatesEquiv m + frequencyCoordinatesEquiv n
    rw [map_add, add_comm]
  have heq : A = B := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    change A (lp.single 2 n c) = B (lp.single 2 n c)
    have hc : lp.single (E := fun _ : frequencyLattice => ℂ) 2 n c =
        c • lp.single (E := fun _ : frequencyLattice => ℂ) 2 n (1 : ℂ) := by
      simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : frequencyLattice => ℂ) 2 n c (1 : ℂ)
    rw [hc, map_smul, map_smul, hsingle]
  exact congrArg (fun U : FourierL2 →L[ℂ] Lp ℂ 2 (volume : Measure T) => U f) heq

end DefocusingNLS

end OAI
