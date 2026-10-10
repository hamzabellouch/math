import OAI.Analysis.BoundedHochschild.TypeIColumnExtension

namespace OAI

/-! A full abelian projection in a faithfully tracial algebra yields a
nonzero finite homogeneous central summand. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_full_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) (hfull : IsCentralSupport p 1) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  classical
  by_contra hfail
  push Not at hfail
  have hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z := hfail
  have hpτ : τ p ≠ 0 := by
    intro hzero
    apply hp0
    apply hfaith p
    simpa only [hp.1.isSelfAdjoint.star_eq, hp.1.isIdempotentElem.eq] using hzero
  have hpτpos : 0 < (τ p).re := by
    have hn := Complex.nonneg_iff.mp (τ.map_nonneg hp.1.nonneg)
    have hne : (τ p).re ≠ 0 := by
      intro hzero
      apply hpτ
      apply Complex.ext
      · exact hzero
      · exact hn.2.symm
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt ((τ 1).re / (τ p).re)
  have hbound : (τ 1).re < (N : ℝ) * (τ p).re := (div_lt_iff₀ hpτpos).mp hN
  have hcolumns (n : ℕ) : ∃ v : Fin n → PartialIso M,
      (∀ i, (v i).initial = p) ∧
      (∀ i j, i ≠ j → (v i).final * (v j).final = 0) := by
    induction n with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨v, hi, ho⟩ := ih
      obtain ⟨w, hwi, hwf⟩ := extend_columns_of_no_homogeneous_piece e hno hp hfull v hi ho
      have hcross (i : Fin n) : (v i).final * w.final = 0 := by
        have he := (w.final_proj.le_iff_mul_eq_right (column_sum_projection v ho).one_sub).mp hwf
        calc
          _ = (v i).final * ((1 - ∑ j, (v j).final) * w.final) := by rw [he]
          _ = 0 := by rw [← mul_assoc, column_mul_residual v ho i, zero_mul]
      obtain ⟨u, hui, huo, _⟩ := exists_append_columns v hi ho w hwi hcross
      exact ⟨u, hui, huo⟩
  obtain ⟨v, hi, ho⟩ := hcolumns N
  exact (not_le_of_gt hbound) (column_count_trace_le τ htr v hi ho)

end KadisonRingrose
end BoundedHochschild

end

end OAI
