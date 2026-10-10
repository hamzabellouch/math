import OAI.Analysis.IrrationalRotation.Product.ProductPowerIdentity
import OAI.Analysis.IrrationalRotation.Spectral.ProductDeterminant
import OAI.Analysis.IrrationalRotation.Analysis.OrbitInvariance
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

private def shiftPowerUnit (n : ℕ) : (Hilbert →L[ℂ] Hilbert)ˣ where
  val := shiftOperator ^ n
  inv := star (shiftOperator ^ n)
  val_inv := Unitary.mul_star_self_of_mem ((unitary _).pow_mem shiftOperator_mem_unitary n)
  inv_val := Unitary.star_mul_self_of_mem ((unitary _).pow_mem shiftOperator_mem_unitary n)

theorem weightedOperator_orbit_inclusion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hinv : (1 - p) * weightedOperator θ c * p = 0)
    (n : ℕ) :
    (1 - star (shiftOperator ^ n) * p * shiftOperator ^ n) *
      positiveCocycleMultiplier θ c hθ0 hc n * p = 0 := by
  exact OrbitInvariance.orbit_inclusion_pow hp hinv n (shiftPowerUnit n)
    (positiveCocycleMultiplier θ c hθ0 hc n)
    (weightedOperator_pow_eq_shift_mul_positiveCocycleMultiplier θ c hθ0 hc hθ n)

theorem shifted_projection_mem_factor (θ : ℕ → ℝ)
    {p : Hilbert →L[ℂ] Hilbert} (hp : p ∈ factor θ) (n : ℕ) :
    star (shiftOperator ^ n) * p * shiftOperator ^ n ∈ factor θ := by
  have hu : shiftOperator ∈ factor θ :=
    subset_vonNeumannGenerated _ (Set.mem_union_left _ (Set.mem_singleton _))
  have hpow : shiftOperator ^ n ∈ factor θ := pow_mem hu n
  have hs : star (shiftOperator ^ n) ∈ factor θ := star_mem hpow
  exact mul_mem (mul_mem hs hp) hpow

theorem shifted_projection_isStarProjection
    {p : Hilbert →L[ℂ] Hilbert} (hp : IsStarProjection p) (n : ℕ) :
    IsStarProjection (star (shiftOperator ^ n) * p * shiftOperator ^ n) := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) :=
    ⟨shiftOperator ^ n, (unitary _).pow_mem shiftOperator_mem_unitary n⟩
  exact hp.map (Unitary.conjStarAlgAut ℂ (Hilbert →L[ℂ] Hilbert) u).symm.toStarAlgHom

end Invariant233.ProductModel

end

end OAI
