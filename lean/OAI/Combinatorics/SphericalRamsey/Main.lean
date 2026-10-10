import OAI.Combinatorics.SphericalRamsey.Ramsey
import OAI.Combinatorics.SphericalRamsey.CopyInvariant
import OAI.Combinatorics.SphericalRamsey.RealDerivation
import OAI.Combinatorics.SphericalRamsey.Parameter
import OAI.Combinatorics.SphericalRamsey.WitnessCoordinates

namespace OAI

noncomputable section
namespace GrahamSpherical

/-- A single actual real derivation defines avoiding colorings in all dimensions. -/
theorem exists_common_derivation_colorings :
    ∃ D : Derivation ℤ ℝ ℝ,
      D parameter = (1 + parameter ^ 2) / 2 ∧
      ∀ n : ℕ, AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) := by
  obtain ⟨D, hD⟩ := exists_real_derivation parameter
    ((1 + parameter ^ 2) / 2) parameter_transcendental
  exact ⟨D, hD, fun _ => derivationColor_avoids D hD⟩

/-- The literal twelve-point spherical witness defeats fifty colors in every
positive dimension, hence is not Euclidean Ramsey. No auxiliary premise remains. -/
theorem full_main : Specification.FullAuthoredResult := by
  obtain ⟨D, _hD, hcolors⟩ := exists_common_derivation_colorings
  apply assemble_full_result witness_ncard witness_subset_sphere
  intro n _hn
  exact ⟨energyColor (derivationEnergy (n := n) D), hcolors n⟩

end GrahamSpherical

end

end OAI
