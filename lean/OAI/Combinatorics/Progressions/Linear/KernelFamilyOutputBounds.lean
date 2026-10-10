import OAI.Combinatorics.Progressions.Estimates.InactiveShortLogBounds

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem exists_kernelFamily_output_bounds {Q α J : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)] [∀ q, Fintype (N q)]
    {L : ℕ} (hL : 0 < L) (x : J → IntegerScalarCubeBox α L)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q))
    (hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0)
    (δ R : Q → ℝ≥0) :
    ∃ Cap Lip Ro : ℝ≥0, 1 ≤ Cap ∧ ∀ (H : Q → ℝ) (hH : ∀ q, 0 < H q),
      let E := fun q => normalizedPivotEquiv _ (hs q)
        (fun i => kernelJetCoefficientScale J (degree q) L (H q) (s q i)) (fun _ => H q)
        (fun i => kernelJetCoefficientScale_pos J (degree q) (by exact_mod_cast hL) (hH q) (s q i))
        (fun _ => hH q)
      let F := fun q => matrixSupCLM (normalizedIntegerColumns
        (remainingMatrixColumns (scalarKernelIntegerJet x (degree q) (rows q)) (s q))
        (fun j => kernelJetCoefficientScale J (degree q) L (H q) j.val) (fun _ => H q))
      (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q)
        ((δ q)⁻¹^Fintype.card (BoundedIntegerExponent J (degree q))) ≤ Cap) ∧
      (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q)
        (affineProductProfileLip (BoundedIntegerExponent J (degree q)) (δ q)) ≤ Lip) ∧
      (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ Ro) := by
  classical
  let E := fun q => scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)
  let F := fun q => scalarKernelFixedFree x (degree q) (rows q) (s q)
  let caps := fun q => pivotKernelCap (UnselectedColumn (s q)) (E q) (R q)
    ((δ q)⁻¹^Fintype.card (BoundedIntegerExponent J (degree q)))
  let lips := fun q => pivotKernelLip (UnselectedColumn (s q)) (E q) (R q)
    (affineProductProfileLip (BoundedIntegerExponent J (degree q)) (δ q))
  let radii := fun q => normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q)
  refine ⟨1 + ∑ q, caps q, ∑ q, lips q, ∑ q, radii q, ?_, ?_⟩
  · exact le_add_of_nonneg_right (by positivity)
  · intro H hH
    dsimp only
    have hE (q) := scalarKernel_pivot_scale_independent hL x (degree q) (rows q) (s q) (hs q) (hH q)
    have hF (q) := scalarKernel_free_scale_independent x (degree q) (rows q) (s q) (hH q).ne'
    simp_rw [hE, hF]
    refine ⟨fun q => ?_, fun q => ?_, fun q => ?_⟩
    · exact (Finset.single_le_sum (fun r _ => (show 0 ≤ caps r from zero_le)) (Finset.mem_univ q)).trans
        (le_add_of_nonneg_left zero_le_one)
    · exact Finset.single_le_sum (fun r _ => (show 0 ≤ lips r from zero_le)) (Finset.mem_univ q)
    · exact Finset.single_le_sum (fun r _ => (show 0 ≤ radii r from zero_le)) (Finset.mem_univ q)

end Erdos3

end

end OAI
