import OAI.Analysis.BoundedHochschild.CountableMatrixSubalgebra
import OAI.Analysis.BoundedHochschild.PathStages

namespace OAI

/-! Bounded diagonal operators for a countable orthogonal column system.
Their commutation with the generated matrix algebra identifies the diagonal
corner as abelian, without a scalar trace or separability assumption. -/

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma countableColumn_star_mul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (i j : ℕ) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j; exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)

def finiteColumnDiagonal (c : ℕ → PartialIso M) (s : Finset ℕ) (a : M) : M :=
  ∑ i ∈ s, (c i : M) * a * star (c i : M)

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteColumnDiagonal_norm_le (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (s : Finset ℕ) (a : M) :
    ‖finiteColumnDiagonal c s a‖ ≤ ‖a‖ := by
  apply supported_sum_norm_le (fun i => (c i).final) _ (fun i => (c i).final_proj) ho
  · intro i
    change ((c i : M) * star (c i : M)) * ((c i : M) * a * star (c i : M)) = _
    calc
      _ = ((c i : M) * star (c i : M) * (c i : M)) * a * star (c i : M) := by
        simp only [mul_assoc]
      _ = _ := by rw [(c i).mul_star_mul]
  · intro i
    change ((c i : M) * a * star (c i : M)) * ((c i : M) * star (c i : M)) = _
    calc
      _ = (c i : M) * a * (star (c i : M) * (c i : M)) * star (c i : M) := by
        simp only [mul_assoc]
      _ = _ := by rw [show star (c i : M) * (c i : M) = 1 from hi i, mul_one]
  · exact norm_nonneg a
  · intro i _
    calc
      ‖(c i : M) * a * star (c i : M)‖ ≤ ‖(c i : M) * a‖ * ‖star (c i : M)‖ := norm_mul_le _ _
      _ ≤ (1 * ‖a‖) * 1 := by
        gcongr
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (c i).norm_le_one (norm_nonneg _))
        · simpa using (c i).norm_le_one
      _ = ‖a‖ := by ring

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteColumnDiagonal_mul_column (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (s : Finset ℕ) (a : M)
    {i : ℕ} (his : i ∈ s) : finiteColumnDiagonal c s a * (c i : M) = (c i : M) * a := by
  classical
  simp only [finiteColumnDiagonal, Finset.sum_mul, mul_assoc]
  simp [countableColumn_star_mul c hi ho, his]

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_star_mul_finiteColumnDiagonal (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (s : Finset ℕ) (a : M)
    {i : ℕ} (his : i ∈ s) : star (c i : M) * finiteColumnDiagonal c s a = a * star (c i : M) := by
  classical
  simp only [finiteColumnDiagonal, Finset.mul_sum, ← mul_assoc]
  simp [countableColumn_star_mul c hi ho, his]

theorem exists_countable_diagonal_operator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (a : M) :
    ∃ D : M, ‖D‖ ≤ ‖a‖ ∧ (∀ i, D * (c i : M) = (c i : M) * a) ∧
      ∀ i, star (c i : M) * D = a * star (c i : M) := by
  classical
  let U : Ultrafilter (Finset ℕ) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset ℕ)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨D, hD, ht⟩ := exists_predual_ultralimit e U (fun s => finiteColumnDiagonal c s a)
    ‖a‖ (fun s => finiteColumnDiagonal_norm_le c hi ho s a)
  refine ⟨D, hD, ?_, ?_⟩
  · intro i
    have h := HochschildSakai.predual_tendsto_mul_right e (c i : M) ht
    have he : (fun s => finiteColumnDiagonal c s a * (c i : M)) =ᶠ[U]
        (fun _ => (c i : M) * a) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset ℕ)] with s hs
      exact finiteColumnDiagonal_mul_column c hi ho s a (hs (Finset.mem_singleton_self i))
    apply predual_tendsto_unique e h
    intro z
    exact tendsto_const_nhds.congr' (he.mono (fun _ hs => congrArg (fun x : M => e.symm x z) hs.symm))
  · intro i
    have h := HochschildSakai.predual_tendsto_mul_left e (star (c i : M)) ht
    have he : (fun s => star (c i : M) * finiteColumnDiagonal c s a) =ᶠ[U]
        (fun _ => a * star (c i : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset ℕ)] with s hs
      exact column_star_mul_finiteColumnDiagonal c hi ho s a (hs (Finset.mem_singleton_self i))
    apply predual_tendsto_unique e h
    intro z
    exact tendsto_const_nhds.congr' (he.mono (fun _ hs => congrArg (fun x : M => e.symm x z) hs.symm))

end BoundedHochschild.KadisonRingrose

end

end OAI
