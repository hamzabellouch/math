import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockProjection
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockShell

namespace OAI

/-!
# From the velocity projection to actual local block preservation

Fixing the selected coordinate projection is exactly preservation of
that block and its complement. This translates the proved velocity
argument into the local subgroup statement used to choose a transverse
shearing shell.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlockProjection_fixed_iff {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S) (g : G n) :
    slMatrixConjugation g (blockProjection (singleBlockSetoid S) k) =
        blockProjection (singleBlockSetoid S) k ↔
      g ∈ blockMatrixGroup (blockComplementSetoid S) := by
  rw [slMatrixConjugation_eq_self_iff]
  constructor
  · intro hcomm
    apply mem_blockMatrixGroup_of_cross_zero
    intro i j hij
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hcomm.eq
    rw [blockProjection_singleBlock_eq S k hk, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    change ¬(i ∈ S ↔ j ∈ S) at hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
      simpa only [ite_eq_left hi, ite_eq_right hj, one_mul, mul_zero] using he
    · have hj : j ∈ S := by
        by_contra hj
        exact hij ⟨fun h => (hi h).elim, fun h => (hj h).elim⟩
      simpa only [ite_eq_right hi, ite_eq_left hj, zero_mul, mul_one] using he.symm
  · intro hg
    exact commute_singleBlockProjection_of_cross_zero S k hk g.val
      (cross_zero_of_mem_blockMatrixGroup (blockComplementSetoid S) g hg)

theorem local_singleBlock_of_fixed_projection {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S)
    (hlocal : {g : L | slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
      blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : L)) :
    {g : L | g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∈ 𝓝 (1 : L) := by
  filter_upwards [hlocal] with g hg
  exact (singleBlockProjection_fixed_iff S k hk g.val).mp hg

/-- The actual velocity-support conclusion gives precisely the local
block containment needed by `exists_small_transverse_shell`. -/
theorem singleBlock_velocity_local_stabilizer {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (hroot : ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j,
      ¬(i ∈ S ↔ j ∈ S) → V i j = 0) :
    {g : L | g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∈ 𝓝 (1 : L) :=
  local_singleBlock_of_fixed_projection L S k hk
    (singleBlockProjection_fixed_near_identity L S k l hkl hk hl hroot hsupport)

end DukePrimeDegree

end

end OAI
