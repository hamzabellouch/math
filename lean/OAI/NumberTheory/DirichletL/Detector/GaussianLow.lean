import OAI.NumberTheory.DirichletL.Detector.GaussianDecomposition
import OAI.NumberTheory.DirichletL.Detector.LowCompletion

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0<Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)

theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI
