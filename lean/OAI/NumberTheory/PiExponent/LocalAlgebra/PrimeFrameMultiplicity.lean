import OAI.NumberTheory.PiExponent.Approximation.FrameResidueDirections
import OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity
import OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent

namespace OAI

noncomputable section
namespace PiExponent

open scoped BigOperators
open PiExponentApprox PiExponentApprox.TransverseMultiplicity
open FrameTransverseMultiplicity NormalBasisRigidity

theorem prime_frame_rectangular_length_lower (m k : ℕ)
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (B : Fin k → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    (I : Ideal (FramePolynomial m)) (cost : Fin (m + 1) → ℝ)
    (n : Fin k → ℕ) (delta : ℝ) (hn : ∀ i, 2 ≤ n i)
    (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ delta)
    (hvanish : ∀ p ∈ I, ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ delta → polynomialFrameWord m word p ∈ Q) :
    (∏ i, n i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (FramePolynomial m) (Localization.AtPrime Q))) := by
  let rho := algebraMap (Localization.AtPrime Q) Q.ResidueField
  let tau := localizedFrameTaylor m k B Q.primeCompl rho
  have hzero : ∀ x, MvPowerSeries.constantCoeff (tau x) = rho x :=
    localizedFrameTaylor_constant m k B Q.primeCompl rho
  have hfirst : ∀ j x, MvPowerSeries.coeff (Finsupp.single j 1) (tau x) =
      primeLocalDirectional Q
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j)) x := by
    intro j x
    apply prime_localizedTaylor_firstCoefficient Q
      (frameTaylor m k B rho) (frameTaylor_constant m k B rho)
      (fun j => frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))
    intro l p
    rw [frameTaylor_firstCoefficient]
    dsimp only [rho]
    rw [← IsScalarTower.algebraMap_apply]
    exact residue_polynomialFrame_eq_frameBasis_dot m (primeResidueMap Q).toRingHom hy (B l) p
  have hCot := prime_rectangular_mapCotangent_surjective Q tau hzero
    (fun j => frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j)) hB hfirst n hn
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ RingHom.ker rho := by
    rw [show RingHom.ker rho = IsLocalRing.maximalIdeal (Localization.AtPrime Q)
      from IsLocalRing.ker_residue]
  apply frame_rectangular_length_lower m k B Q.primeCompl rho
    IsLocalRing.residue_surjective (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) hP
    I cost n delta (rectangularPositive n hn) hcost hbudget hCot
  intro p hp word hword
  dsimp only [rho]
  rw [← IsScalarTower.algebraMap_apply]
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hvanish p hp word hword)

end PiExponent
end

end OAI
