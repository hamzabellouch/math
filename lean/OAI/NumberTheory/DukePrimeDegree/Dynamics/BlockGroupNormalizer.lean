import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockNormalizer

namespace OAI

/-!
# Normalizers of the concrete block matrix group

The block-scalar algebra is the full matrix commutant of the block
matrix group. Consequently a group normalizer preserves that algebra,
and its identity component lies in the block matrix group itself.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_diagonal_of_commute_regular {n : ℕ}
    (ell : Fin n → ℝ) (hell : Function.Injective ell)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hc : Commute M (Matrix.diagonal (fun i => Real.exp (ell i)))) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hc.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hn : Real.exp (ell j) - Real.exp (ell i) ≠ 0 := by
      intro h
      exact hij ((hell (Real.exp_injective (sub_eq_zero.mp h))).symm)
    have hz : M i j * (Real.exp (ell j) - Real.exp (ell i)) = 0 := by nlinarith [he]
    exact (mul_eq_zero.mp hz).resolve_right hn

lemma blockScalar_mem_iff_commute_blockMatrixGroup {d : ℕ}
    (r : Setoid (Fin (d + 1))) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    M ∈ blockScalarAlgebra r ↔ ∀ h : blockMatrixGroup r, Commute M h.val.val := by
  constructor
  · intro hM h
    obtain ⟨hD, hc⟩ := (mem_blockScalarAlgebra_iff r M).mp hM
    apply (slMatrixConjugation_eq_self_iff h.val M).mp
    rw [hD]
    exact h.property _ hc
  · intro hM
    have hell : Function.Injective (regularDiagonalWeights d) := by
      intro i j he
      by_contra hij
      have hgap := regularDiagonalWeights_separated d i j hij
      rw [he, sub_self, abs_zero] at hgap
      norm_num at hgap
    have hcomm := hM ⟨diagonalOneParameter (regularDiagonalWeights d)
      (regularDiagonalWeights_sum d) 1,
      diagonalOneParameter_mem_blockMatrixGroup r _ _ _⟩
    have hD : M = Matrix.diagonal (fun i => M i i) := by
      apply matrix_diagonal_of_commute_regular _ hell M
      simpa only [diagonalOneParameter, mul_one] using hcomm
    apply (mem_blockScalarAlgebra_iff r M).mpr
    refine ⟨hD, ?_⟩
    intro i j hr
    by_cases hij : i = j
    · subst j; rfl
    · have hroot := hM ⟨Matrix.SpecialLinearGroup.transvection hij (1 : ℝ),
        transvection_mem_blockMatrixGroup r i j hij hr⟩
      rw [hD] at hroot
      exact (diagonal_commute_transvection_iff _ hij).mp hroot

lemma conjugate_blockScalar_mem_of_group_normalizer {d : ℕ}
    (r : Setoid (Fin (d + 1))) (g : G (d + 1))
    (hg : g ∈ Subgroup.normalizer (blockMatrixGroup r : Set (G (d + 1))))
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hM : M ∈ blockScalarAlgebra r) :
    slMatrixConjugation g M ∈ blockScalarAlgebra r := by
  apply (blockScalar_mem_iff_commute_blockMatrixGroup r _).mpr
  intro h
  have hk : g * h.val * g⁻¹ ∈ blockMatrixGroup r :=
    ((Subgroup.mem_normalizer_iff.mp hg) h.val).mp h.property
  have he : slMatrixConjugation g (g * h.val * g⁻¹).val = h.val.val := by
    have hc : (g * h.val * g⁻¹).val = slMatrixConjugation g⁻¹ h.val.val := by
      simp only [slMatrixConjugation, inv_inv, Matrix.SpecialLinearGroup.coe_mul]
    rw [hc]
    exact slMatrixConjugation_inverse g h.val.val
  have hcomm := ((blockScalar_mem_iff_commute_blockMatrixGroup r M).mp hM
    ⟨g * h.val * g⁻¹, hk⟩).map (slMatrixConjugationHom g)
  change Commute (slMatrixConjugation g M)
    (slMatrixConjugation g (g * h.val * g⁻¹).val) at hcomm
  rwa [he] at hcomm

/-- A normalizer of the block group also normalizes its full matrix
commutant, which is the block-scalar algebra. -/
theorem blockMatrixGroup_normalizer_le_scalarNormalizer {d : ℕ}
    (r : Setoid (Fin (d + 1))) :
    Subgroup.normalizer (blockMatrixGroup r : Set (G (d + 1))) ≤ blockScalarNormalizer r := by
  intro g hg M
  constructor
  · intro hM
    have hi := (Subgroup.normalizer (blockMatrixGroup r : Set (G (d + 1)))).inv_mem hg
    have he := conjugate_blockScalar_mem_of_group_normalizer r g⁻¹ hi _ hM
    simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using he
  · exact conjugate_blockScalar_mem_of_group_normalizer r g hg M

/-- Every connected subgroup normalizing the concrete block group is
already block diagonal. -/
theorem connected_blockMatrixGroup_normalizer_le {d : ℕ}
    (r : Setoid (Fin (d + 1))) (H : Subgroup (G (d + 1))) [PreconnectedSpace H]
    (hH : H ≤ Subgroup.normalizer (blockMatrixGroup r : Set (G (d + 1)))) :
    H ≤ blockMatrixGroup r := by
  intro h hh
  exact connected_normalizer_mem_blockMatrixGroup r (fun g : H => g.val)
    continuous_subtype_val 1 rfl
    (fun g => blockMatrixGroup_normalizer_le_scalarNormalizer r (hH g.property)) ⟨h, hh⟩

end DukePrimeDegree

end

end OAI
