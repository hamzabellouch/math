import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockTransverseDiagonal
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransverseStabilizerLimit
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Sequences

namespace OAI

/-!
# Local invariance under the full neutral block group

Within-block root invariance and full diagonal invariance suffice for
invariance under a neighborhood of the identity in the block group.
The proof uses the already constructed finite Gaussian elimination:
a small block matrix outside the subgroup would normalize to a positive
scalar determinant-one matrix still outside it, which is impossible.
Disconnected block components are not asserted to preserve the measure.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem block_subgroup_mem_nhds_of_roots_and_diagonals {n : ℕ}
    (hn : n ≠ 0) (r : Setoid (Fin n)) (L : Subgroup (G n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), r i j → ∀ t : ℝ,
      SpecialLinearGroup.transvection hij t ∈ L)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      diagonalOneParameter v hv t ∈ L) :
    {g : blockMatrixGroup r | g.val ∈ L} ∈ 𝓝 (1 : blockMatrixGroup r) := by
  let B := blockMatrixGroup r
  let M := L ⊓ B
  by_contra hnot
  have hcl : (1 : B) ∈ closure ({g : B | g.val ∈ L}ᶜ) := by
    rw [closure_compl]
    intro hi
    exact hnot (mem_interior_iff_mem_nhds.mp hi)
  obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.mp hcl
  let g : ℕ → G n := fun k => (u k).val
  have hg : Tendsto g atTop (𝓝 (1 : G n)) := by
    simpa only [g, Function.comp_def, Subgroup.coe_one] using
      continuous_subtype_val.continuousAt.tendsto.comp hulim
  have hgnot (k : ℕ) : g k ∉ L := hu k
  have hrootM (i j : Fin n) (hij : i ≠ j) (hr : r i j) (t : ℝ) :
      SpecialLinearGroup.transvection hij t ∈ M := by
    refine ⟨hroot i j hij hr t, ?_⟩
    apply mem_blockMatrixGroup_of_cross_zero r
    intro a b hab
    change (Matrix.transvection i j t) a b = 0
    have habne : a ≠ b := fun he => hab (he ▸ r.refl a)
    have hpair : ¬(i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact hab hr
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne habne,
      Matrix.single_apply, ite_eq_right hpair, add_zero]
  have hdiagM (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ) :
      diagonalOneParameter v hv t ∈ M :=
    ⟨hdiag v hv t, diagonalOneParameter_mem_blockMatrixGroup r v hv t⟩
  obtain ⟨s, b, c, _hs, _hb, he, hm, hc, hz⟩ :=
    exists_scalar_block_transverse_sequence hn r M hrootM hdiagM g hg
  obtain ⟨k, hk⟩ := hz.exists
  have hsB : s k ∈ B := by
    rw [he k]
    exact B.mul_mem (u k).property (hm k).2
  have hsnot : s k ∉ L := by
    rw [he k]
    exact right_corrected_not_mem L (hgnot k) (hm k).1
  have hsne : s k ≠ 1 := by
    intro h
    exact hsnot (h ▸ L.one_mem)
  obtain ⟨i, j, hij, hentry⟩ := exists_cross_block_entry_of_scalar_diagonal
    hn r (s k) (c k) (hc k) hk.1 hk.2 hsne
  exact hentry (cross_zero_of_mem_blockMatrixGroup r (s k) hsB i j hij)

/-- The actual stabilizer contains an open subgroup of the neutral
block group. This is the form needed for a local neutral product chart. -/
theorem open_block_stabilizer_of_roots_and_diagonals {n : ℕ}
    (hn : n ≠ 0) (r : Setoid (Fin n)) (μ : Measure (X n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), r i j → ∀ t : ℝ,
      μ.map (fun x => rightAction x (SpecialLinearGroup.transvection hij t)) = μ)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ) :
    IsOpen (((invariantRightSubgroup μ).comap (blockMatrixGroup r).subtype :
      Subgroup (blockMatrixGroup r)) : Set (blockMatrixGroup r)) :=
  Subgroup.isOpen_of_mem_nhds _
    (block_subgroup_mem_nhds_of_roots_and_diagonals hn r
      (invariantRightSubgroup μ) hroot hdiag)

end DukePrimeDegree

end

end OAI
