import OAI.NumberTheory.PiExponent.Jets.TaylorRectangular

namespace OAI

noncomputable section
namespace PiExponent.FrameTransverseMultiplicity

open scoped BigOperators
open PiExponentApprox
open CommutingTaylor TaylorRectangular
open TransverseMultiplicity

variable {L K : Type*} [CommRing L] [Field K]

def frameTaylor (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) :
    FramePolynomial m →+* MvPowerSeries (Fin k) K :=
  residueTaylorFin k (fun i => rationalFrame m (B i))
    (rho.comp (algebraMap (FramePolynomial m) L))

@[simp] theorem frameTaylor_constant (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) (a : FramePolynomial m) :
    MvPowerSeries.constantCoeff (frameTaylor m k B rho a) =
      rho (algebraMap (FramePolynomial m) L a) := by
  exact constantCoeff_residueTaylorFin _ _ _ _

def localizedFrameTaylor (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) : L →+* MvPowerSeries (Fin k) K :=
  localizedTaylorMap M (frameTaylor m k B rho) rho (frameTaylor_constant m k B rho)

@[simp] theorem localizedFrameTaylor_algebraMap (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (a : FramePolynomial m) :
    localizedFrameTaylor m k B M rho (algebraMap (FramePolynomial m) L a) =
      frameTaylor m k B rho a := by
  exact localizedTaylorMap_algebraMap M _ rho _ a

@[simp] theorem localizedFrameTaylor_constant (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (a : L) :
    MvPowerSeries.constantCoeff (localizedFrameTaylor m k B M rho a) = rho a := by
  exact RingHom.congr_fun (localizedTaylorMap_constant M (frameTaylor m k B rho) rho
    (frameTaylor_constant m k B rho)) a

@[simp] theorem frameTaylor_firstCoefficient (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) (i : Fin k) (a : FramePolynomial m) :
    MvPowerSeries.coeff (Finsupp.single i 1) (frameTaylor m k B rho a) =
      rho (algebraMap (FramePolynomial m) L (polynomialFrame m (B i) a)) := by
  exact coeff_single_residueTaylorFin _ _ _ i a

variable [Algebra ℚ K]

theorem localizedFrameTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (I : Ideal (FramePolynomial m))
    (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      rho (algebraMap (FramePolynomial m) L (polynomialFrameWord m word a)) = 0) :
    I.map (algebraMap (FramePolynomial m) L) ≤
      (rectangularIdeal (K := K) n).comap (localizedFrameTaylor m k B M rho) := by
  apply localizedTaylorMap_ideal_le M (frameTaylor m k B rho) rho (frameTaylor_constant m k B rho)
  exact frame_residueTaylor_ideal_le m k B (rho.comp (algebraMap (FramePolynomial m) L))
    I cost n δ hcost hn hvanish

def frameRectangularHom (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (n : Fin k → ℕ) :
    L →ₐ[ℚ] (MvPowerSeries (Fin k) K ⧸ rectangularIdeal (K := K) n) :=
  rectangularTaylorAlgHom n (localizedFrameTaylor m k B M rho)

theorem frameRectangularHom_maps_residueIdeal (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (P : Ideal L) (hP : P ≤ RingHom.ker rho) :
    P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap
      (frameRectangularHom m k B M rho n) :=
  rectangularTaylorAlgHom_maps_residueIdeal n hn _ rho
    (localizedFrameTaylor_constant m k B M rho) P hP

theorem frame_rectangular_length_lower (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (hrho : Function.Surjective rho)
    (P : Ideal L) (hP : P ≤ RingHom.ker rho) (I : Ideal (FramePolynomial m))
    (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hn : ∀ i, 0 < n i) (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn))
        (frameRectangularHom m k B M rho n)
        (frameRectangularHom_maps_residueIdeal m k B M rho n hn P hP)))
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      rho (algebraMap (FramePolynomial m) L (polynomialFrameWord m word a)) = 0) :
    (∏ i, n i : ℕ) ≤
      Module.length L (L ⧸ I.map (algebraMap (FramePolynomial m) L)) := by
  apply rectangularTaylor_length_lower n hn (localizedFrameTaylor m k B M rho) rho hrho
    (localizedFrameTaylor_constant m k B M rho) P _ hP hCot
  exact localizedFrameTaylor_ideal_le m k B M rho I cost n δ hcost hbudget hvanish

end PiExponent.FrameTransverseMultiplicity

end

end OAI
