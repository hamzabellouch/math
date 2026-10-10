import OAI.Analysis.KadisonSimilarity.Tracial.MatrixStageGrowth

namespace OAI

/-! The generating matrix stages, viewed internally in their generated
von Neumann algebra. This retains the actual operators and matrix sizes. -/

noncomputable section
namespace KadisonSimilarity

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H} (F : ℕ → FiniteMatrixStage N)

def generatedInternalStage (n : ℕ) :
    FiniteMatrixStage (FiniteMatrixStage.generatedVonNeumann F) := by
  let E := F n
  have hm (i j : Fin E.size) : (E.units.entry i j).val ∈ FiniteMatrixStage.generated F :=
    FiniteMatrixStage.stage_le_generated F n
      ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem i j))
  refine { size := E.size, positive := E.positive, units := ?_ }
  refine {
    entry := fun i j => ⟨(E.units.entry i j).val, hm i j⟩
    star_entry := ?_
    mul_entry := ?_
    total := ?_ }
  · intro i j
    apply Subtype.ext
    exact congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H)) (E.units.star_entry i j)
  · intro i j k l
    apply Subtype.ext
    have h := congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H))
      (E.units.mul_entry i j k l)
    split_ifs at h ⊢ <;> exact h
  · apply Subtype.ext
    change (FiniteMatrixStage.generated F).subtype
      (∑ i, (⟨(E.units.entry i i).val, hm i i⟩ : FiniteMatrixStage.generated F)) = 1
    rw [map_sum]
    trans ∑ i, N.toStarSubalgebra.subtype (E.units.entry i i)
    · exact Finset.sum_congr rfl (fun _ _ => rfl)
    · have h := congrArg N.toStarSubalgebra.subtype E.units.total
      simpa only [map_sum, map_one] using h

@[simp] theorem generatedInternalStage_size (n : ℕ) :
    (generatedInternalStage F n).size = (F n).size := rfl

theorem generatedInternalStage_sizes_cofinal [Nontrivial N.toStarSubalgebra]
    (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) :
    ∀ m : ℕ, ∃ j, m < (generatedInternalStage F j).size := by
  intro m
  obtain ⟨j, hj⟩ := matrix_stage_sizes_cofinal F hmono hdiff (m + 1)
  exact ⟨j, lt_of_lt_of_le (Nat.lt_succ_self m) hj⟩

end KadisonSimilarity

end

end OAI
