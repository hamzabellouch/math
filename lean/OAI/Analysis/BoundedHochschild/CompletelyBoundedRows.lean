import OAI.Analysis.BoundedHochschild.FiniteRightAveraging

namespace OAI

/-!
# The finite-row consequence of complete boundedness

The definition uses the usual entrywise amplifications on actual C*-matrix
algebras. In the properly infinite case, the proved isometry columns turn
this definition into precisely the row estimate needed for right averaging.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A uniform bound on all entrywise matrix amplifications of a linear map. -/
def CompletelyBoundedEstimate (T : M →L[ℂ] M) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (A : CStarMatrix (Fin n) (Fin n) M), ‖A.map T‖ ≤ C * ‖A‖

omit [PartialOrder M] [StarOrderedRing M] in
lemma left_isometry_norm {v : M} (hv : star v * v = 1) (a : M) : ‖v * a‖ = ‖a‖ := by
  have h : star (v * a) * (v * a) = star a * a := by
    rw [star_mul]
    calc
      _ = star a * (star v * v) * a := by simp only [mul_assoc]
      _ = star a * a := by rw [hv, mul_one]
  have hn : ‖v * a‖ ^ 2 = ‖a‖ ^ 2 := by
    simpa only [CStarRing.norm_star_mul_self, ← sq] using congrArg norm h
  nlinarith [norm_nonneg (v * a), norm_nonneg a]

variable {n : ℕ} (c : Fin n → PartialIso M)
  (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma columnRow_mul_isometry (x : Fin n → M) (j : Fin n) :
    columnRow c x * (c j : M) = x j := by
  classical
  calc
    _ = ∑ i, x i * (star (c i : M) * (c j : M)) := by
      simp only [columnRow, Finset.sum_mul, mul_assoc]
    _ = x j := by simp [column_star_mul c hi ho]

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma columnCompression_row (x : Fin n → M) (k i j : Fin n) :
    columnCompression c ((c k : M) * columnRow c x) i j = if i = k then x j else 0 := by
  change star (c i : M) * ((c k : M) * columnRow c x) * (c j : M) = _
  calc
    _ = (star (c i : M) * (c k : M)) * (columnRow c x * (c j : M)) := by
      simp only [mul_assoc]
    _ = _ := by rw [column_star_mul c hi ho, columnRow_mul_isometry c hi ho]; split_ifs <;> simp

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Complete boundedness implies the finite-row estimate used by the module
projection, via the actual finite matrix amplifications already constructed. -/
theorem finiteRowBound_of_completelyBounded (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : HasFiniteRowBound T C := by
  refine ⟨hT.1, ?_⟩
  intro n x
  cases n with
  | zero => simp
  | succ n =>
      obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
      let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      have hmap : (columnCompression c ((c k : M) * columnRow c x)).map T =
          columnCompression c ((c k : M) * columnRow c (fun i => T (x i))) := by
        ext i j
        rw [CStarMatrix.map_apply, columnCompression_row c hi ho, columnCompression_row c hi ho]
        split_ifs <;> simp
      have hb := hT.2 (n + 1) (columnCompression c ((c k : M) * columnRow c x))
      rw [hmap, columnCompression_norm c hi ho hs, columnCompression_norm c hi ho hs,
        left_isometry_norm (hi k), left_isometry_norm (hi k)] at hb
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow, columnRow_norm_sq c hi ho, columnRow_norm_sq c hi ho] at hb2
      exact hb2

/-- The finite elementary averages in the module projection are bounded by
any complete bound for the original linear map. -/
theorem finiteRightAverage_norm_of_completelyBounded
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (m : Fin (n + 1) → M) (hm : ∑ i, m i * star (m i) = 1)
    (T : M →L[ℂ] M) {C : ℝ} (hT : CompletelyBoundedEstimate T C) :
    ‖finiteRightAverage m T‖ ≤ C := by
  obtain ⟨c, hi, ho, _⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
  exact finiteRightAverage_norm_of_rowBound c hi ho m hm T
    (finiteRowBound_of_completelyBounded e hno T hT)

end BoundedHochschild.KadisonRingrose

end

end OAI
