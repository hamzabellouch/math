import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockLocalStabilizer

namespace OAI

/-!
# Why an incident one-way root prevents the two-block argument

A nonzero root crossing the selected block moves its coordinate projection.
If the stabilizer contains the entire root, it cannot preserve that block
on any identity neighborhood. Thus a terminal strongly connected class
cannot be substituted for a symmetric root block while incoming roots
remain. This states the precise obstruction to that proposed reduction.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma cross_root_not_mem_blockComplement {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (hcross : ¬(i ∈ S ↔ j ∈ S)) {t : ℝ} (ht : t ≠ 0) :
    SpecialLinearGroup.transvection hij t ∉ blockMatrixGroup (blockComplementSetoid S) := by
  intro hm
  have hz := cross_zero_of_mem_blockMatrixGroup (blockComplementSetoid S)
    (SpecialLinearGroup.transvection hij t) hm i j hcross
  have he : t = 0 := by
    simpa only [SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply,
      and_self, ite_true, zero_add] using hz
  exact ht he

lemma cross_root_moves_blockProjection {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S)
    {i j : Fin n} (hij : i ≠ j) (hcross : ¬(i ∈ S ↔ j ∈ S))
    {t : ℝ} (ht : t ≠ 0) :
    slMatrixConjugation (SpecialLinearGroup.transvection hij t)
      (blockProjection (singleBlockSetoid S) k) ≠
        blockProjection (singleBlockSetoid S) k := by
  intro he
  exact cross_root_not_mem_blockComplement S hij hcross ht
    ((singleBlockProjection_fixed_iff S k hk _).mp he)

/-- Arbitrarily small elements of an incident root already rule out
local containment in the two-block group. No entropy premise is used. -/
theorem not_local_block_containment_of_cross_root {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (hcross : ¬(i ∈ S ↔ j ∈ S))
    (hroot : ∀ t : ℝ, SpecialLinearGroup.transvection hij t ∈ L) :
    {g : L | g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∉ 𝓝 (1 : L) := by
  intro hlocal
  let a : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  let u : ℕ → L := fun m => ⟨SpecialLinearGroup.transvection hij (a m), hroot _⟩
  have hlarge : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlarge
  have hu : Tendsto u atTop (𝓝 (1 : L)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [u, Function.comp_def, Subgroup.coe_one,
      SpecialLinearGroup.transvection_coeff_zero] using
      (continuous_rootTransvection hij).continuousAt.tendsto.comp ha
  obtain ⟨m, hm⟩ := (hu.eventually hlocal).exists
  exact cross_root_not_mem_blockComplement S hij hcross (by
    dsimp only [a]
    positivity) hm

end DukePrimeDegree

end

end OAI
