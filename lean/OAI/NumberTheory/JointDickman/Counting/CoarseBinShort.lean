import OAI.NumberTheory.JointDickman.Analysis.LaplaceBinShort
import OAI.NumberTheory.JointDickman.Counting.UnitBinEnergy
import OAI.NumberTheory.JointDickman.Analysis.CoarseLaplaceApproximation

namespace OAI

/-! # Actual coarse prime features have centered bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem unit_coarse_short_with_center
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (d : Fin m)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B d)) r (H B) z‖^2) < ε := by
  intro ε hε
  obtain ⟨P,hP⟩ := primeCoarseFeature_laplace_approximation hSD hSW hM hMP hm d
    (show 0 < ε/384 by positivity)
  have hpoly := unit_laplace_short_with_center hMR hMRT hKMT hM hJ ζ μ hmean
    auxiliaryPrimes auxiliaryPrimes_prime (range (P.natDegree+1)) P.coeff
    (q := q) A scale H hA hscale hH (ε/8) (by positivity)
  filter_upwards [hP,hpoly,hH.eventually_ge_atTop 1] with B hPB hpolyB hHB
  have herr := unit_prime_feature_error ζ hζ μ hμ (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (primeCoarseFeature m B d)
    (fun x => ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)
    hHB (hA B) scale hscale (q := q) (show 0 < ε/16 by positivity)
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [hpolyB,herr,hX.eventually_gt_atTop 0] with n hpolyN herrN hXn
  intro r
  have he := unitProgressionBinAverage_energy_triangle
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B d))
    (primeSiteWeight (auxiliaryPrimes B)
      (fun x => ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x))
    r (by linarith : 0 < H B) hXn
  have hp := hpolyN r
  have hr := herrN (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) r
  nlinarith

end JointDickman

end OAI
