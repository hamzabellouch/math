import OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson
import OAI.NumberTheory.DirichletL.Detector.PhysicalReopen

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dite_eq_left hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (supportedElement_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dite_eq_right hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end SevenEighths.ProbePhysical
end

end OAI
