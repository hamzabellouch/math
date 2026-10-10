import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorCube
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCubeTerm
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness

namespace OAI

/-! Small square divisors act on the actual nonzero stopped rows. Zero
coefficients impose no artificial coprimality condition on the ambient support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_stopped_active_coprime_small (ℓ : ℤ) {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e d : Eisenstein) (hd : d ≠ 0)
    (hsmall : norm d < min (X^ξ) (geometricBinLower (1+δ) X h))
    {a : Eisenstein} (ha : a ∈ stoppedIntervalSupport ι X l b e)
    (ha0 : angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early) a ≠ 0) : IsCoprime a d := by
  have ha' := stoppedIntervalSupport_spec X l b e ha
  apply rough_coprime_small ha'.1 ha'.2.1 hd hsmall
  intro p hp
  exact angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) 0
    (1+δ) Z Q W (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
    (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
    j k h early hj ha0 (primaryPrimeFactor_spec ha'.1 hp).1
    (primaryPrimeFactor_spec ha'.1 hp).2


lemma angular_stopped_divisor_cube_eq (ℓ : ℤ) {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e d : Eisenstein) (hd : primary d) (hds : Squarefree d)
    (hsmall : norm d < min (X^ξ) (geometricBinLower (1+δ) X h))
    (u : ℝ) (Φ : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    let S := stoppedIntervalSupport ι X l b e
    let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early)
    divisorCubePoissonContribution d S β u Φ A =
      (1/(norm d)^2:ℝ)*cubePoissonContribution S β u Φ A := by
  apply divisorCubePoissonContribution_eq_of_active hd hds
  · intro a ha
    exact (stoppedIntervalSupport_spec X l b e ha).1
  · intro a ha ha0
    exact angular_stopped_active_coprime_small ℓ hX hξz hδ hδone W j k h Z Q early hj
      e d (primary_ne_zero hd) hsmall ha ha0
  · exact hA

end CubicFirstMoment

end

end OAI
