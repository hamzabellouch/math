import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockRootGroup
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootVelocityRecovery

namespace OAI

/-!
# The commutant of a block-supported actual velocity space

An element of a subgroup always conjugates its own velocity space to
itself. Once that space has the block support found by recurrence and
contains the within-block root directions, its commutant is the block
scalar algebra (when no block is a singleton). This gives the full
normalizer conclusion directly, without assuming that the subgroup is
normalized by the diagonal group or invoking a Lie subgroup theorem.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_mem_velocitySpace {n : ℕ}
    (L : Subgroup (G n)) {g : G n} (hg : g ∈ L)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ matrixVelocitySpace L) :
    slMatrixConjugation g V ∈ matrixVelocitySpace L := by
  have hconj : ∀ h ∈ L, g⁻¹ * h * (g⁻¹)⁻¹ ∈ L := by
    intro h hh
    simpa only [inv_inv] using L.mul_mem (L.mul_mem (L.inv_mem hg) hh) hg
  simpa only [slMatrixConjugation, inv_inv] using
    conjugate_mem_matrixVelocitySpace L L g⁻¹ hconj hV

theorem blockScalar_mem_iff_commute_velocitySpace {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hnosingle : ∀ i, ∃ j, i ≠ j ∧ r i j)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j, ¬r i j → V i j = 0)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ blockScalarAlgebra r ↔ ∀ V ∈ matrixVelocitySpace L, Commute M V := by
  constructor
  · intro hM V hV
    exact ((commute_blockScalars_iff r V).mpr (hsupport V hV) M hM).symm
  · intro hM
    apply (blockScalar_mem_iff_commute_blockRoots r hnosingle M).mpr
    intro i j hij hr
    have hV : Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L :=
      ⟨fun t => Matrix.SpecialLinearGroup.transvection hij t,
        hroot i j hij hr,
        by simpa only [mul_one] using hasIdentityMatrixDerivative_rootCurve hij 1⟩
    exact (Commute.one_right M).add_right (hM _ hV)

theorem subgroup_le_blockScalarNormalizer_of_velocity_support {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hnosingle : ∀ i, ∃ j, i ≠ j ∧ r i j)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j, ¬r i j → V i j = 0) :
    L ≤ blockScalarNormalizer r := by
  have hconj (g : G n) (hg : g ∈ L) (M : Matrix (Fin n) (Fin n) ℝ)
      (hM : M ∈ blockScalarAlgebra r) :
      slMatrixConjugation g M ∈ blockScalarAlgebra r := by
    apply (blockScalar_mem_iff_commute_velocitySpace L r hnosingle hroot hsupport _).mpr
    intro V hV
    have hback := slMatrixConjugation_mem_velocitySpace L (L.inv_mem hg) hV
    have hc := ((blockScalar_mem_iff_commute_velocitySpace L r hnosingle hroot hsupport M).mp hM
      _ hback).map (slMatrixConjugationHom g)
    change Commute (slMatrixConjugation g M)
      (slMatrixConjugation g (slMatrixConjugation g⁻¹ V)) at hc
    simpa only [slMatrixConjugation_inverse] using hc
  intro g hg M
  constructor
  · intro hM
    have hback := hconj g⁻¹ (L.inv_mem hg) _ hM
    simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using hback
  · exact hconj g hg M

end DukePrimeDegree

end

end OAI
