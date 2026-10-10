import OAI.Analysis.BoundedHochschild.MultimodularColumns
import OAI.Analysis.BoundedHochschild.CompletelyBoundedPrimitives

namespace OAI

/-! A bounded multimodular cochain has completely bounded last slices if
the coefficient subalgebra contains unital isometry columns of every finite
size. This is the required matrix-norm specialization, with no dimension
factor in the bound. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma columnDiagonal_eq_reconstruction {m : ℕ} (c : Fin m → PartialIso M) (a : M) :
    columnDiagonal c a = columnReconstruction c (matrixScalarHom m a) := by
  classical
  simp [columnDiagonal, columnReconstruction, matrixScalarHom_apply]

lemma columnReconstruction_norm_for_multimodular {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (A : CStarMatrix (Fin m) (Fin m) M) :
    ‖columnReconstruction c A‖ = ‖A‖ := by
  rw [← columnCompression_norm c hi ho hs (columnReconstruction c A),
    columnCompression_reconstruction c hi ho]

lemma columnDiagonal_norm_le {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (a : M) : ‖columnDiagonal c a‖ ≤ ‖a‖ := by
  rw [columnDiagonal_eq_reconstruction, columnReconstruction_norm_for_multimodular c hi ho hs]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma multimodular_matrix_identity {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hc : ∀ i, (c i : M) ∈ R) (a : Fin n → M) (A : CStarMatrix (Fin m) (Fin m) M) :
    f (Fin.snoc (fun k => columnDiagonal c (a k)) (columnReconstruction c A)) =
      columnReconstruction c (A.map (f.curryRight a)) := by
  classical
  calc
    _ = (f.curryRight (fun k => columnDiagonal c (a k)))
        (∑ i, ∑ j, (c i : M) * A i j * star (c j : M)) := rfl
    _ = ∑ i, ∑ j, f (Fin.snoc (fun k => columnDiagonal c (a k))
        ((c i : M) * A i j * star (c j : M))) := by
      simp only [map_sum, ContinuousMultilinearMap.curryRight_apply]
    _ = ∑ i, ∑ j, (c i : M) * f (Fin.snoc a (A i j)) * star (c j : M) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact multimodular_column_term f hf c hi ho hc a (A i j) i j
    _ = _ := rfl

lemma multimodular_last_matrix_bound {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (hc : ∀ i, (c i : M) ∈ R)
    (a : Fin n → M) (A : CStarMatrix (Fin m) (Fin m) M) :
    ‖A.map (f.curryRight a)‖ ≤ (‖f‖ * ∏ k, ‖a k‖) * ‖A‖ := by
  rw [← columnReconstruction_norm_for_multimodular c hi ho hs (A.map (f.curryRight a)),
    ← multimodular_matrix_identity f hf c hi ho hc a A]
  calc
    _ ≤ (‖f‖ * ∏ k, ‖columnDiagonal c (a k)‖) * ‖columnReconstruction c A‖ :=
      f.norm_map_snoc_le _ _
    _ ≤ (‖f‖ * ∏ k, ‖a k‖) * ‖A‖ := by
      rw [columnReconstruction_norm_for_multimodular c hi ho hs]
      gcongr with k
      exact columnDiagonal_norm_le c hi ho hs (a k)

theorem lastSliceEstimate_of_multimodular_columns {R : StarSubalgebra ℂ M} {n : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (hcols : ∀ m : ℕ, ∃ c : Fin (m + 1) → PartialIso M,
      (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      (∑ i, (c i).final = 1) ∧ ∀ i, (c i : M) ∈ R) :
    LastSliceEstimate f ‖f‖ := by
  refine ⟨norm_nonneg _, fun a => ⟨by positivity, fun m A => ?_⟩⟩
  cases m with
  | zero =>
      have hA : A = 0 := by ext i; exact Fin.elim0 i
      have hB : A.map (f.curryRight a) = 0 := by ext i; exact Fin.elim0 i
      rw [hB, hA, norm_zero, mul_zero]
  | succ m =>
      obtain ⟨c, hi, ho, hs, hc⟩ := hcols m
      exact multimodular_last_matrix_bound f hf c hi ho hs hc a A

theorem primitive_of_multimodular_columns [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M))
    {R : StarSubalgebra ℂ M} {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver R f)
    (hcols : ∀ m : ℕ, ∃ c : Fin (m + 1) → PartialIso M,
      (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      (∑ i, (c i).final = 1) ∧ ∀ i, (c i : M) ∈ R)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_lastSliceEstimate P f (lastSliceEstimate_of_multimodular_columns f hf hcols)
    hcocycle

end BoundedHochschild.KadisonRingrose

end

end OAI
