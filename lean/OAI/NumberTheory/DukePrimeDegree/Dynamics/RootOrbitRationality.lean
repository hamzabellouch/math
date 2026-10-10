import OAI.NumberTheory.DukePrimeDegree.Geometry.RootMatrixDensity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockRootGroup

namespace OAI

/-!
# Prime-degree obstruction for finite root-group orbits

Polynomial recurrence replaces the full diagonal subgroup in the matrix
density argument. The result applies to any finite-volume orbit group L
that contains the block roots and preserves the blocks. For the root-
generated group itself, fixed-vector recurrence first excludes singletons.
No finite-volume-orbit existence assertion is assumed or proved here.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem centralizer_subset_blockScalar_of_finite_root_orbit {n : ℕ}
    (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (r : Setoid (Fin n)) (hnosingle : ∀ i, ∃ j, i ≠ j ∧ r i j)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    M ∈ blockScalarAlgebra r := by
  let F := conjugationOrbitMap g L M hM
  let ν := μ.map F
  have hF : Continuous F := continuous_conjugationOrbitMap g L M hM
  have hrootdist (i j : Fin n) (hij : i ≠ j) (hr : r i j) :
      ν.map (rootMatrixConjugation i j 1) = ν := by
    rw [← slMatrixConjugation_root i j hij]
    have hm : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L := by
      simpa only [Matrix.SpecialLinearGroup.transvection_inv] using L.inv_mem (hroot i j hij hr)
    exact conjugationOrbitMap_map_invariant g L M hM μ hinv
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hm⟩
  have hcomm : ∀ᵐ N ∂ν, ∀ i j, i ≠ j → r i j →
      Commute N (Matrix.transvection i j (1 : ℝ)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · by_cases hr : r i j
      · exact (ae_commute_root_of_conjugation_invariance ν i j hij (hrootdist i j hij hr)).mono
          (fun _ h _ _ => h)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hr h).elim)
  have hae : ∀ᵐ x ∂μ, F x ∈ blockScalarAlgebra r :=
    ae_of_ae_map hF.measurable.aemeasurable
      (hcomm.mono fun N h => (blockScalar_mem_iff_commute_blockRoots r hnosingle N).mpr h)
  have hclosed : IsClosed (F ⁻¹' (blockScalarAlgebra r : Set (Matrix (Fin n) (Fin n) ℝ))) :=
    (blockScalarAlgebra r).toSubmodule.closed_of_finiteDimensional.preimage hF
  have hbase : (Quotient.mk _ (1 : L) : LatticeOrbitQuotient g L) ∈ μ.support := by
    rw [latticeOrbit_support_eq_univ g L μ hμ hinv]
    trivial
  have he := Measure.support_subset_of_isClosed hclosed hae hbase
  change conjugationOrbitMap g L M hM (Quotient.mk _ (1 : L)) ∈ blockScalarAlgebra r at he
  rwa [conjugationOrbitMap_identity] at he

theorem rationalBlockRealSpan_of_centralizer_image {n : ℕ}
    (g : G n) (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hcent : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (∀ s : pointOrbitStabilizer g L, Commute M s.val.val) → M ∈ blockScalarAlgebra r)
    (hblock : L ≤ blockMatrixGroup r)
    {c : Fin n → ℝ} (hc : c ∈ blockCoordinateAlgebra r) :
    c ∈ rationalBlockRealSpan g r := by
  have hdiag (B : Matrix (Fin n) (Fin n) ℚ)
      (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
      (fun i => slMatrixConjugation g (rationalMatrixCast B) i i) ∈
        rationalBlockStabilizer g r := by
    have hD := (mem_blockScalarAlgebra_iff r _).mp (hcent _ (by
      intro s
      obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g L s
      rw [← hγ]
      exact ((commute_rationalMatrixCast_iff B (latticeStabilizerMatrix g L γ)).mpr
        ((mem_commutatorFamily_ker _ _).mp hB γ)).map (slMatrixConjugationHom g)))
    change (slMatrixConjugation g (rationalMatrixCast B) =
      Matrix.diagonal (fun i => slMatrixConjugation g (rationalMatrixCast B) i i)) ∧
      (∀ i j, r i j → slMatrixConjugation g (rationalMatrixCast B) i i =
        slMatrixConjugation g (rationalMatrixCast B) j j) at hD
    refine ⟨?_, hD.2⟩
    apply (mem_rationalDiagonalStabilizer_iff_rational_matrix g _).mpr
    refine ⟨B, ?_⟩
    rw [← hD.1]
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    change rationalMatrixCast B * g.val = g.val * (g⁻¹.val * rationalMatrixCast B * g.val)
    simp only [← mul_assoc, hg, one_mul]
  let A := slMatrixConjugation g⁻¹ (Matrix.diagonal c)
  have hA : A ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker := by
    rw [mem_commutatorFamily_ker]
    intro γ
    let h : L := ⟨(MulAut.conj g⁻¹)
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val), γ.property⟩
    have he : h.val.val = slMatrixConjugation g
        (rationalMatrixCast (latticeStabilizerMatrix g L γ)) := by
      rw [rationalMatrixCast_latticeStabilizer]
      simp only [h, slMatrixConjugation, MulAut.conj_apply, inv_inv,
        Matrix.SpecialLinearGroup.coe_mul]
    have Hc := (blockMatrixGroup_commute r ⟨h.val, hblock h.property⟩ c hc).map
      (slMatrixConjugationHom g⁻¹)
    change Commute A (slMatrixConjugation g⁻¹ h.val.val) at Hc
    rw [he] at Hc
    simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using Hc
  rw [latticeStabilizer_commutant_rational] at hA
  let T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin n → ℝ) :=
    (LinearMap.pi fun i => (LinearMap.proj i).comp (LinearMap.proj i)).comp
      (slMatrixConjugationLinear g)
  have hspan : Submodule.span ℝ (rationalMatrixCast ''
      ((commutatorFamily (latticeStabilizerMatrix g L)).ker :
        Set (Matrix (Fin n) (Fin n) ℚ))) ≤ (rationalBlockRealSpan g r).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨B, hB, rfl⟩
    exact Submodule.subset_span ⟨⟨_, hdiag B hB⟩, rfl⟩
  have hT : T A ∈ rationalBlockRealSpan g r := hspan hA
  have hTA : T A = c := by
    change (fun i => slMatrixConjugation g (slMatrixConjugation g⁻¹ (Matrix.diagonal c)) i i) = c
    rw [slMatrixConjugation_inverse]
    funext i
    exact Matrix.diagonal_apply_eq c i
  rwa [hTA] at hT

/-- This applies to the actual larger orbit group L, provided it contains
the non-singleton block roots and preserves the blocks. -/
theorem root_partition_universal_of_finite_root_containing_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (L : Subgroup (G n)) (μ : Measure (LatticeOrbitQuotient g L))
    [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (r : Setoid (Fin n)) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (hnosingle : ∀ i, ∃ j, i ≠ j ∧ r i j)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hblock : L ≤ blockMatrixGroup r) : ∀ i j, r i j := by
  apply root_partition_universal_of_rational_span hn g hgeneric r hnontrivial
  intro c hc
  exact rationalBlockRealSpan_of_centralizer_image g L r
    (centralizer_subset_blockScalar_of_finite_root_orbit g L μ hμ hinv r hnosingle hroot)
    hblock hc

/-- A generic finite-volume orbit of the nontrivial root-generated group
in prime degree already forces the root partition to be universal. -/
theorem root_partition_universal_of_generic_finite_blockRoot_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (r : Setoid (Fin n)) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (μ : Measure (LatticeOrbitQuotient g (blockRootGroup r))) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0)
    (hinv : ∀ h : blockRootGroup r,
      μ.map (fun x => latticeOrbitRightAction g (blockRootGroup r) x h) = μ) :
    ∀ i j, r i j := by
  apply root_partition_universal_of_finite_root_containing_orbit hn g hgeneric
    (blockRootGroup r) μ hμ hinv r hnontrivial
    (no_singleton_block_of_generic_finite_root_orbit g hgeneric r hnontrivial μ hμ hinv)
    (fun i j hij hr => root_mem_blockRootGroup r i j hij hr 1)
    (blockRootGroup_le_blockMatrixGroup r)

end DukePrimeDegree

end

end OAI
