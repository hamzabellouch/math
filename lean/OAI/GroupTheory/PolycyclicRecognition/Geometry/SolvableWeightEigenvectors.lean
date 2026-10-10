import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableFaithfulRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DerivationEigenvectors

namespace OAI

/-! # Real eigenvectors span the finite weight representation -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "e" => cartanNilshadowEquiv T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableWeightDerivation_eigenspaces_span (c : ℕ) (x : L) :
    derivationEigenvectorSpan (truncatedEnvelopingDerivation c
      (nilshadowWeightDerivation T H x)) = ⊤ := by
  let D := truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
  let S := derivationEigenvectorSubalgebra D
    (truncatedEnvelopingDerivation_one c _)
    (truncatedEnvelopingDerivation_mul c _)
  have hgen (v : K) : truncatedEnvelopingGenerator (R := ℝ) c v ∈ S := by
    obtain ⟨v, rfl⟩ := (e).surjective v
    apply cartan_root_induction T H (x := v)
    · intro χ v hv
      apply Submodule.mem_iSup_of_mem (cartanHeightWeight T H χ (heightProjection T.character x))
      rw [Module.End.mem_eigenspace_iff]
      change truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
        (truncatedEnvelopingGenerator c (e v)) = _
      rw [truncatedEnvelopingDerivation_generator, nilshadowWeightDerivation_equiv,
        heightSemisimpleAction_apply_root T H x χ hv, map_smul, map_smul]
    · simpa only [map_zero] using S.zero_mem
    · intro v w hv hw
      simpa only [map_add] using S.add_mem hv hw
  have hle : (⊤ : Subalgebra ℝ (Q c)) ≤ S := by
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hgen _
  apply top_unique
  intro u _
  exact hle (by trivial)

end PolycyclicRecognition

end

end OAI
