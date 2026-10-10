import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedSlabLower
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity

namespace OAI

/-! Continuity and global boundedness of the actual slab field, including
its discontinuous density at the slab boundary. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabDensity_nonnegative {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (x : Position) :
    0 ≤ slabDensity rho H S x := by
  by_cases hx : x ∈ slabDomain H S
  · simpa [slabDensity, hx] using hrho
  · simp [slabDensity, hx]

theorem slabDensity_le {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (x : Position) :
    slabDensity rho H S x ≤ rho := by
  by_cases hx : x ∈ slabDomain H S
  · simp [slabDensity, hx]
  · simpa [slabDensity, hx] using hrho

theorem slabPotential_eq_negativePotentialOf (rho H S : ℝ) :
    slabPotential rho H S = fun x => -NeutralAtom.potentialOf (slabDensity rho H S) x := rfl

theorem slabPotential_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) : Continuous (slabPotential rho H S) := by
  rw [slabPotential_eq_negativePotentialOf]
  exact (NeutralAtom.potentialOf_continuous (slabDensity_integrable hH hS rho)
    (slabDensity_nonnegative hrho H S) (slabDensity_le hrho H S)).neg

theorem slabPotential_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabPotential rho H S x| ≤
      rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho := by
  have hb := (NeutralAtom.potential_integrable_and_bound
    (slabDensity_integrable hH hS rho) (slabDensity_nonnegative hrho H S)
    (by norm_num : (0:ℝ)<1) (fun y _ => slabDensity_le hrho H S y) (x := x)).2
  rw [slabDensity_integral] at hb
  rw [slabPotential_eq_negativePotentialOf, abs_neg,
    abs_of_nonneg (NeutralAtom.potentialOf_nonneg (slabDensity_nonnegative hrho H S) x)]
  simpa only [inv_one, one_mul] using hb

theorem manufacturedSlabPotential_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    Continuous (manufacturedSlabPotential rho H S freq scale u) :=
  ((slabPotential_continuous hrho hH hS).sub continuous_const).add
    (manufacturedWellField_C7 freq scale S u).continuous

theorem manufacturedSlabPotential_bounded {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 < S) (freq scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    ∃ B : ℝ, ∀ x, |manufacturedSlabPotential rho H S freq scale u x| ≤ B := by
  obtain ⟨C,hC⟩ := (manufacturedWellField_C7 freq scale S u).continuous.bounded_above_of_compact_support
    (manufacturedWellField_compact freq scale hS u)
  let A := rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho
  refine ⟨2*A+C,fun x => ?_⟩
  have hx := slabPotential_abs_bound hrho hH hS.le x
  have h0 := slabPotential_abs_bound hrho hH hS.le 0
  have hw := hC x
  change |manufacturedWellField freq scale S u x| ≤ C at hw
  unfold manufacturedSlabPotential
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add hx h0)) hw).trans_eq (by dsimp [A]; ring))

end ContinuumCoulomb

end

end OAI
