import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation

namespace OAI

/-! Compactness and entry bounds for the actual special orthogonal group. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma specialOrthogonal_entry_bound {N : ℕ} (U : SpecialOrthogonal N) (i j : Fin N) :
    |(U : Matrix (Fin N) (Fin N) ℝ) i j| ≤ 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1
  have hrow : (∑ k, ((U : Matrix (Fin N) (Fin N) ℝ) i k)^2) = 1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two]
      using congrFun (congrFun hU i) i
  have hs : ((U : Matrix (Fin N) (Fin N) ℝ) i j)^2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  exact (sq_le_one_iff_abs_le_one _).mp hs

lemma isClosed_specialOrthogonal (N : ℕ) :
    IsClosed (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) := by
  have he : (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) =
      {A | A*A.transpose=1} ∩ {A | A.det=1} := by
    ext A
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,SetLike.mem_coe,
      Matrix.mem_specialOrthogonalGroup_iff,Matrix.mem_orthogonalGroup_iff]
  rw [he]
  apply IsClosed.inter
  · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

lemma isCompact_specialOrthogonal (N : ℕ) :
    IsCompact (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) := by
  have hb : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      Set.pi Set.univ fun _ : Fin N => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  apply hb.of_isClosed_subset (isClosed_specialOrthogonal N)
  intro A hA
  simp only [Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Icc]
  intro i j
  exact abs_le.mp (specialOrthogonal_entry_bound ⟨A,hA⟩ i j)

instance specialOrthogonal_compactSpace (N : ℕ) : CompactSpace (SpecialOrthogonal N) :=
  isCompact_iff_compactSpace.mp (isCompact_specialOrthogonal N)

end InvariantIsing

end

end OAI
