import OAI.NumberTheory.DirichletL.Reflection.PowerfulBudget
import OAI.NumberTheory.DirichletL.Reflection.RowReindex

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (parents : Finset (Ideal Eis)) (Q : Ideal Eis),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ∀ (E : ℝ) (f : Ideal Eis→ℝ),0≤E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal Eis) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      exact mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun T _ => hblocks A T))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end SevenEighths.InverseReflectedPhase

end OAI
