import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalCommutatorCurve
import OAI.NumberTheory.DukePrimeDegree.Dynamics.NormalizerOrbitReduction

namespace OAI

/-!
# Selecting a positive-mass orbit of an open subgroup

An open subgroup has countable index in the second-countable matrix
groups used here. A finite invariant measure on a larger orbit therefore
has a nonzero restriction to one smaller orbit. The generic full set is
preserved by restriction, allowing the basepoint to be chosen there.
No connectedness of the larger homogeneous group is needed.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma countable_quotient_of_open_subgroup {n : ℕ} (L : Subgroup (G n))
    (H : Subgroup L) (hopen : IsOpen (H : Set L)) : Countable (L ⧸ H) := by
  let : SecondCountableTopology L := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology (L ⧸ H) := QuotientGroup.instSecondCountableTopology H
  let : DiscreteTopology (L ⧸ H) := QuotientGroup.discreteTopology hopen
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

lemma larger_orbit_covered_by_subgroup_orbits {n : ℕ}
    (g : G n) (L H : Subgroup (G n)) (_hHL : H ≤ L) :
    range (latticeOrbitPoint g L) ⊆
      ⋃ c : L ⧸ H.comap L.subtype, range (latticeOrbitPoint (g * c.out.val) H) := by
  rintro _ ⟨x, rfl⟩
  induction x using Quotient.inductionOn with
  | h a =>
    let c : L ⧸ H.comap L.subtype := QuotientGroup.mk a
    have hrel : QuotientGroup.leftRel (H.comap L.subtype) c.out a :=
      Quotient.exact (Quotient.out_eq' c)
    rw [QuotientGroup.leftRel_apply] at hrel
    let h : H := ⟨(c.out⁻¹ * a).val, hrel⟩
    refine mem_iUnion.mpr ⟨c, ⟨Quotient.mk _ h, ?_⟩⟩
    change Quotient.mk _ ((g * c.out.val) * (c.out⁻¹ * a).val) =
      (Quotient.mk _ (g * a.val) : X n)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

lemma latticeOrbitPoint_range_mul {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    range (latticeOrbitPoint (g * h.val) H) = range (latticeOrbitPoint g H) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Quotient.inductionOn with
    | h a =>
      refine ⟨Quotient.mk _ (h * a), ?_⟩
      change Quotient.mk _ (g * (h * a).val) =
        (Quotient.mk _ ((g * h.val) * a.val) : X n)
      rw [Subgroup.coe_mul, mul_assoc]
  · rintro ⟨y, rfl⟩
    induction y using Quotient.inductionOn with
    | h a =>
      refine ⟨Quotient.mk _ (h⁻¹ * a), ?_⟩
      change Quotient.mk _ ((g * h.val) * (h⁻¹ * a).val) =
        (Quotient.mk _ (g * a.val) : X n)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

lemma restrict_orbit_invariant {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) (μ : Measure (X n))
    (hinv : ∀ h : H, μ.map (fun x => rightAction x h.val) = μ) (h : H) :
    (μ.restrict (range (latticeOrbitPoint g H))).map (fun x => rightAction x h.val) =
      μ.restrict (range (latticeOrbitPoint g H)) := by
  have hs := (latticeOrbitPoint_measurableEmbedding g H hH).measurableSet_range
  have he := Measure.restrict_map (μ := μ) (continuous_rightAction h.val).measurable hs
  rw [hinv h, latticeOrbitPoint_range_preimage g H h] at he
  exact he.symm

/-- An actual larger orbit decomposes into countably many orbits of an
open subgroup, one of which has positive measure. -/
theorem exists_nonzero_subgroup_orbit_restriction {n : ℕ}
    (g : G n) (L H : Subgroup (G n)) (hHL : H ≤ L)
    (hopen : IsOpen ((H.comap L.subtype : Subgroup L) : Set L))
    (μ : Measure (X n)) (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L)) :
    ∃ g' : G n, μ.restrict (range (latticeOrbitPoint g' H)) ≠ 0 := by
  let C := L ⧸ H.comap L.subtype
  let : Countable C := countable_quotient_of_open_subgroup L (H.comap L.subtype) hopen
  let S : C → Set (X n) := fun c => range (latticeOrbitPoint (g * c.out.val) H)
  by_contra hnone
  have hzero (c : C) : μ (S c) = 0 := by
    apply Measure.restrict_eq_zero.mp
    by_contra hne
    exact hnone ⟨g * c.out.val, hne⟩
  have hall : ∀ᵐ x ∂μ, ∀ c : C, x ∉ S c := by
    rw [ae_all_iff]
    intro c
    exact ae_iff.mpr (by simpa using hzero c)
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x, hx, havoid⟩ := (horbit.and hall).exists
  obtain ⟨c, hc⟩ := mem_iUnion.mp (larger_orbit_covered_by_subgroup_orbits g L H hHL hx)
  exact havoid c hc

/-- The prime-degree obstruction needs only an open block-preserving
subgroup of the actual finite-volume orbit group. -/
theorem root_partition_universal_of_open_blockSubgroup_orbit {n : ℕ}
    (hn : n.Prime) (g : G n) (L : Subgroup (G n))
    (hL : IsClosed (L : Set (G n)))
    (r : Setoid (Fin n)) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (hopen : IsOpen (((blockMatrixGroup r).comap L.subtype : Subgroup L) : Set L))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L))
    (hinv : ∀ h : L, μ.map (fun x => rightAction x h.val) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    ∀ i j, r i j := by
  let H := L ⊓ blockMatrixGroup r
  have hH : IsClosed (H : Set (G n)) := hL.inter (isClosed_blockMatrixGroup r)
  have hopenH : IsOpen ((H.comap L.subtype : Subgroup L) : Set L) := by
    have he : H.comap L.subtype = (blockMatrixGroup r).comap L.subtype := by
      ext h
      change (h.val ∈ L ∧ h.val ∈ blockMatrixGroup r) ↔ h.val ∈ blockMatrixGroup r
      exact and_iff_right h.property
    rw [he]
    exact hopen
  obtain ⟨g', hnonzero⟩ := exists_nonzero_subgroup_orbit_restriction g L H inf_le_left
    hopenH μ hμ horbit
  let ν := μ.restrict (range (latticeOrbitPoint g' H))
  have hν : ν ≠ 0 := hnonzero
  have hs := (latticeOrbitPoint_measurableEmbedding g' H hH).measurableSet_range
  have hνorbit : ∀ᵐ x ∂ν, x ∈ range (latticeOrbitPoint g' H) := ae_restrict_mem hs
  have hνgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 :=
    ae_restrict_of_ae hgeneric
  have : NeBot (ae ν) := ae_neBot.mpr hν
  obtain ⟨x, hx, hxgeneric⟩ := (hνorbit.and hνgeneric).exists
  obtain ⟨y, rfl⟩ := hx
  induction y using Quotient.inductionOn with
  | h a =>
    have hg' : ∀ v ∈ rowLattice (g' * a.val).val, v ≠ 0 → ∀ j, v j ≠ 0 := hxgeneric
    apply root_partition_universal_of_generic_blockPreserving_orbit_measure hn (g' * a.val)
      hg' H hH ν hν
    · rwa [latticeOrbitPoint_range_mul]
    · exact restrict_orbit_invariant g' H hH μ
        (fun h => hinv ⟨h.val, h.property.1⟩)
    · exact hnontrivial
    · intro i j hij hr
      exact ⟨hroot i j hij hr, transvection_mem_blockMatrixGroup r i j hij hr⟩
    · exact inf_le_right

end DukePrimeDegree

end

end OAI
