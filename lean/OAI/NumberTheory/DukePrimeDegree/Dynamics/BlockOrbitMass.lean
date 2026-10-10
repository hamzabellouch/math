import OAI.NumberTheory.DukePrimeDegree.Dynamics.PairedOrbitSupport

namespace OAI

/-!
# Positive mass on a block orbit already gives the prime-degree obstruction

The finite measure is assumed invariant only under the chosen opposite
root pair.  Restricting it to one positive block orbit preserves those
two maps.  The rational commutant argument therefore rules out every
proper block partition, without full invariance under the block group.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma transvection_neg_one_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (i j : Fin n) (hij : i ≠ j) (hr : r i j) :
    Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ blockMatrixGroup r := by
  simpa only [Matrix.SpecialLinearGroup.transvection_inv] using
    (blockMatrixGroup r).inv_mem (transvection_mem_blockMatrixGroup r i j hij hr)

lemma latticeOrbitPoint_comap_invariant_element {n : ℕ}
    (g : G n) (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (μ : Measure (X n)) (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L))
    (h : L) (hinv : μ.map (fun x => rightAction x h.val) = μ) :
    (μ.comap (latticeOrbitPoint g L)).map
      (fun x => latticeOrbitRightAction g L x h) = μ.comap (latticeOrbitPoint g L) := by
  let F := latticeOrbitPoint g L
  let R := fun x => latticeOrbitRightAction g L x h
  have hF := latticeOrbitPoint_measurableEmbedding g L hL
  have hmap := latticeOrbitPoint_map_comap g L hL μ horbit
  apply hF.map_injective
  calc
    _ = (μ.comap F).map (F ∘ R) :=
      Measure.map_map hF.measurable (continuous_latticeOrbitRightAction g L h).measurable
    _ = (μ.comap F).map ((fun x => rightAction x h.val) ∘ F) := by
      congr 1
      funext x
      exact latticeOrbitPoint_rightAction g L x h
    _ = ((μ.comap F).map F).map (fun x => rightAction x h.val) :=
      (Measure.map_map (continuous_rightAction h.val).measurable hF.measurable).symm
    _ = μ := by rw [hmap, hinv]
    _ = (μ.comap F).map F := hmap.symm

theorem partition_universal_of_root_pair_supported_on_block_orbit {n : ℕ}
    (hn : n.Prime) (g : G n) (r : Setoid (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g (blockMatrixGroup r)))
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ))) = μ)
    (hopinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ))) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0) :
    ∀ a b, r a b := by
  let L := blockMatrixGroup r
  have hL : IsClosed (L : Set (G n)) := isClosed_blockMatrixGroup r
  let ν := μ.comap (latticeOrbitPoint g L)
  have hmap : ν.map (latticeOrbitPoint g L) = μ :=
    latticeOrbitPoint_map_comap g L hL μ horbit
  have hν : ν ≠ 0 := by
    intro hzero
    rw [hzero, Measure.map_zero] at hmap
    exact hμ hmap.symm
  have hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L :=
    transvection_neg_one_mem_blockMatrixGroup r i j hij hr
  have hopposite : Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ) ∈ L :=
    transvection_neg_one_mem_blockMatrixGroup r j i hij.symm (r.symm hr)
  have hνgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice (latticeOrbitPoint g L x),
      v ≠ 0 → ∀ k, v k ≠ 0 :=
    ae_of_ae_map (continuous_latticeOrbitPoint g L).measurable.aemeasurable
      (by rwa [hmap])
  have hscalar (M : Matrix (Fin n) (Fin n) ℝ)
      (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
      ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    obtain ⟨c, hc⟩ := realStabilizer_scalar_of_root_pair_measure hn g L ν hν
      i j hij hroot hopposite
      (latticeOrbitPoint_comap_invariant_element g L hL μ horbit ⟨_, hroot⟩ hinv)
      (latticeOrbitPoint_comap_invariant_element g L hL μ horbit ⟨_, hopposite⟩ hopinv)
      hνgeneric (slMatrixConjugation g⁻¹ M)
      (inverseConjugate_mem_realStabilizer g L M hM)
    refine ⟨c, ?_⟩
    have he := congrArg (slMatrixConjugation g) hc
    rwa [slMatrixConjugation_inverse, slMatrixConjugation_smul_one] at he
  intro a b
  by_contra hab
  let c : Fin n → ℝ := fun k => if r k a then 1 else 0
  have hc : c ∈ blockCoordinateAlgebra r := by
    intro k l hkl
    have he : r k a ↔ r l a :=
      ⟨fun h => r.trans (r.symm hkl) h, fun h => r.trans hkl h⟩
    simp only [c, he]
  have hM : ∀ s : pointOrbitStabilizer g L, Commute (Matrix.diagonal c) s.val.val :=
    fun s => blockMatrixGroup_commute r s.val c hc
  obtain ⟨t, ht⟩ := hscalar (Matrix.diagonal c) hM
  have ha := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a a) ht
  have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M b b) ht
  have hba : ¬r b a := fun h => hab (r.symm h)
  simp only [Matrix.diagonal_apply_eq, c, r.refl a, ite_true,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at ha
  simp only [Matrix.diagonal_apply_eq, c, hba, ite_false,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hb
  exact zero_ne_one (hb.trans ha.symm)

/-- Positive mass, not full support, suffices. The root pair must belong
to the same proposed block, so restriction to that orbit remains invariant. -/
theorem partition_universal_of_positive_block_orbit_mass {n : ℕ}
    (hn : n.Prime) (g : G n) (r : Setoid (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hpos : μ (range (latticeOrbitPoint g (blockMatrixGroup r))) ≠ 0)
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ))) = μ)
    (hopinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ))) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0) :
    ∀ a b, r a b := by
  let L := blockMatrixGroup r
  let E := range (latticeOrbitPoint g L)
  have hL : IsClosed (L : Set (G n)) := isClosed_blockMatrixGroup r
  have hE : MeasurableSet E := (latticeOrbitPoint_measurableEmbedding g L hL).measurableSet_range
  have hν : μ.restrict E ≠ 0 := mt Measure.restrict_eq_zero.mp hpos
  have hrestrict (h : L) (hh : μ.map (fun x => rightAction x h.val) = μ) :
      (μ.restrict E).map (fun x => rightAction x h.val) = μ.restrict E := by
    have he := Measure.restrict_map (μ := μ) (continuous_rightAction h.val).measurable hE
    rw [hh, latticeOrbitPoint_range_preimage g L h] at he
    exact he.symm
  exact partition_universal_of_root_pair_supported_on_block_orbit hn g r i j hij hr
    (μ.restrict E) hν (ae_restrict_mem hE)
    (hrestrict ⟨_, transvection_neg_one_mem_blockMatrixGroup r i j hij hr⟩ hinv)
    (hrestrict ⟨_, transvection_neg_one_mem_blockMatrixGroup r j i hij.symm (r.symm hr)⟩ hopinv)
    (ae_restrict_of_ae hgeneric)

end DukePrimeDegree

end

end OAI
