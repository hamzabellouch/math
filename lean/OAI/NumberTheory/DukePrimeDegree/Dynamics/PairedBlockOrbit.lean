import OAI.NumberTheory.DukePrimeDegree.Dynamics.ScalarOrbitCommutant
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OpenSubgroupOrbit

namespace OAI

/-!
# One root pair excludes every proper block partition

The roots required here are just one opposite pair inside the actual finite
orbit group. The partition may combine all singleton coordinates into one
block; no root invariance is required among those coordinates. Thus this
endpoint matches the open block subgroup provided by local projection
fixation, without adding a diagonal-normalization hypothesis.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem partition_universal_of_generic_finite_opposite_root_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (r : Setoid (Fin n)) (hblock : L ≤ blockMatrixGroup r) : ∀ a b, r a b := by
  intro a b
  by_contra hab
  let c : Fin n → ℝ := fun k => if r k a then 1 else 0
  have hc : c ∈ blockCoordinateAlgebra r := by
    intro k l hkl
    have he : r k a ↔ r l a := ⟨fun h => r.trans (r.symm hkl) h, fun h => r.trans hkl h⟩
    simp only [c, he]
  have hM : ∀ s : pointOrbitStabilizer g L,
      Commute (Matrix.diagonal c) s.val.val := by
    intro s
    exact blockMatrixGroup_commute r ⟨s.val.val, hblock s.val.property⟩ c hc
  obtain ⟨t, ht⟩ := pointStabilizer_scalar_of_finite_opposite_root_orbit
    hn g hgeneric L μ hμ hinv i j hij hroot_ij hroot_ji (Matrix.diagonal c) hM
  have ha := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a a) ht
  have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M b b) ht
  have hba : ¬r b a := fun h => hab (r.symm h)
  simp only [Matrix.diagonal_apply_eq, c, r.refl a, ite_true,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at ha
  simp only [Matrix.diagonal_apply_eq, c, hba, ite_false,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hb
  exact zero_ne_one (hb.trans ha.symm)

/-- Transfer to a finite invariant measure on the actual lattice space,
with its closed orbit group explicitly given. -/
theorem partition_universal_of_generic_opposite_root_orbit_measure {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (μ : Measure (X n)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L))
    (hinv : ∀ h : L, μ.map (fun x => rightAction x h.val) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (r : Setoid (Fin n)) (hblock : L ≤ blockMatrixGroup r) : ∀ a b, r a b := by
  let ν := μ.comap (latticeOrbitPoint g L)
  have hν : ν ≠ 0 := by
    intro hzero
    have he := latticeOrbitPoint_map_comap g L hL μ horbit
    change ν.map _ = μ at he
    rw [hzero, Measure.map_zero] at he
    exact hμ he.symm
  exact partition_universal_of_generic_finite_opposite_root_orbit
    hn g hgeneric L ν hν (latticeOrbitPoint_comap_invariant g L hL μ horbit hinv)
    i j hij hroot_ij hroot_ji r hblock

/-- Only an open block-preserving subgroup is needed. The one opposite root
pair lies in it because its two indices belong to the same block. -/
theorem partition_universal_of_open_opposite_root_orbit {n : ℕ}
    (hn : n.Prime) (g : G n) (L : Subgroup (G n))
    (hL : IsClosed (L : Set (G n)))
    (r : Setoid (Fin n))
    (hopen : IsOpen (((blockMatrixGroup r).comap L.subtype : Subgroup L) : Set L))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L))
    (hinv : ∀ h : L, μ.map (fun x => rightAction x h.val) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0) :
    ∀ a b, r a b := by
  let H := L ⊓ blockMatrixGroup r
  have hH : IsClosed (H : Set (G n)) := hL.inter (isClosed_blockMatrixGroup r)
  have hopenH : IsOpen ((H.comap L.subtype : Subgroup L) : Set L) := by
    have he : H.comap L.subtype = (blockMatrixGroup r).comap L.subtype := by
      ext h
      change (h.val ∈ L ∧ h.val ∈ blockMatrixGroup r) ↔ h.val ∈ blockMatrixGroup r
      exact and_iff_right h.property
    rwa [he]
  obtain ⟨g', hnonzero⟩ := exists_nonzero_subgroup_orbit_restriction g L H inf_le_left
    hopenH μ hμ horbit
  let ν := μ.restrict (range (latticeOrbitPoint g' H))
  have hν : ν ≠ 0 := hnonzero
  have hs := (latticeOrbitPoint_measurableEmbedding g' H hH).measurableSet_range
  have hνorbit : ∀ᵐ x ∂ν, x ∈ range (latticeOrbitPoint g' H) := ae_restrict_mem hs
  have hνgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0 :=
    ae_restrict_of_ae hgeneric
  have : NeBot (ae ν) := ae_neBot.mpr hν
  obtain ⟨x, hx, hxgeneric⟩ := (hνorbit.and hνgeneric).exists
  obtain ⟨y, rfl⟩ := hx
  induction y using Quotient.inductionOn with
  | h a =>
    have hg' : ∀ v ∈ rowLattice (g' * a.val).val, v ≠ 0 → ∀ k, v k ≠ 0 := hxgeneric
    have hνorbit' : ∀ᵐ x ∂ν, x ∈ range (latticeOrbitPoint (g' * a.val) H) := by
      rwa [latticeOrbitPoint_range_mul]
    have hνinv : ∀ h : H, ν.map (fun x => rightAction x h.val) = ν :=
      restrict_orbit_invariant g' H hH μ (fun h => hinv ⟨h.val, h.property.1⟩)
    exact partition_universal_of_generic_opposite_root_orbit_measure hn (g' * a.val)
      hg' H hH ν hν hνorbit' hνinv i j hij
      ⟨hroot_ij, transvection_mem_blockMatrixGroup r i j hij hr⟩
      ⟨hroot_ji, transvection_mem_blockMatrixGroup r j i hij.symm (r.symm hr)⟩
      r inf_le_right

end DukePrimeDegree

end

end OAI
