import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombCubeCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedRawModulus

namespace OAI

/-! Coordinatewise Lipschitz control of the actual Coulomb box integrand. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open UniformQuadrature

theorem position_norm_le_sum_abs (x : Position) : ‖x‖ ≤ ∑ i, |x i| := by
  apply (sq_le_sq₀ (norm_nonneg x) (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin 3 => |x i|)
      (fun i _ => abs_nonneg (x i)))

theorem twoParticleCoordinates_sum_abs (v w : Fin 6 → ℝ) :
    (∑ i : Fin 3, |(twoParticleCoordinates v).1 i - (twoParticleCoordinates w).1 i|) +
      (∑ i : Fin 3, |(twoParticleCoordinates v).2 i - (twoParticleCoordinates w).2 i|) =
        ∑ i : Fin 6, |v i - w i| := by
  simp only [twoParticleCoordinates_fst, twoParticleCoordinates_snd]
  exact (Fin.sum_univ_add (a := 3) (b := 3) (fun i : Fin 6 => |v i - w i|)).symm

def rawCoulombSix (freq ε : ℝ) (shift : Position) (v : Fin 6 → ℝ) : ℝ :=
  cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq)
    (twoParticleCoordinates v)

theorem rawCoulombSix_modulus {freq ε L : ℝ} (hf : 0 ≤ freq) (hε : 0 < ε)
    (hL : 0 ≤ L) (shift : Position) :
    cubeModulus (-L) L ((64 + 2 * freq * L) * ε⁻¹ + ε⁻¹ ^ 2)
      (rawCoulombSix freq ε shift) := by
  intro v hv w hw
  have hv0 : |(positionSplitCoordinates (twoParticleCoordinates v).1).2| ≤ L := by
    change |(twoParticleCoordinates v).1 2| ≤ L
    rw [twoParticleCoordinates_fst]
    exact abs_le.mpr (hv _)
  have hv1 : |(positionSplitCoordinates (twoParticleCoordinates v).2).2| ≤ L := by
    change |(twoParticleCoordinates v).2 2| ≤ L
    rw [twoParticleCoordinates_snd]
    exact abs_le.mpr (hv _)
  have hw0 : |(positionSplitCoordinates (twoParticleCoordinates w).1).2| ≤ L := by
    change |(twoParticleCoordinates w).1 2| ≤ L
    rw [twoParticleCoordinates_fst]
    exact abs_le.mpr (hw _)
  have hw1 : |(positionSplitCoordinates (twoParticleCoordinates w).2).2| ≤ L := by
    change |(twoParticleCoordinates w).2 2| ≤ L
    rw [twoParticleCoordinates_snd]
    exact abs_le.mpr (hw _)
  have ht := cappedRawPair_modulus hf hε shift
    (twoParticleCoordinates v).1 (twoParticleCoordinates v).2
    (twoParticleCoordinates w).1 (twoParticleCoordinates w).2 hv0 hv1 hw0 hw1
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hx := position_norm_le_sum_abs ((twoParticleCoordinates v).1 - (twoParticleCoordinates w).1)
  have hy := position_norm_le_sum_abs ((twoParticleCoordinates v).2 - (twoParticleCoordinates w).2)
  simpa only [PiLp.sub_apply, twoParticleCoordinates_sum_abs] using add_le_add hx hy

end ContinuumCoulomb

end

end OAI
