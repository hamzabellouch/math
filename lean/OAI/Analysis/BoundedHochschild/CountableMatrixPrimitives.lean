import OAI.Analysis.BoundedHochschild.CountableMatrixTypeI
import OAI.Analysis.BoundedHochschild.MultimodularMatrixBound

namespace OAI

/-! The type-I matrix subalgebra and the final cohomological step for its
multimodular cocycles. Reduction of an ordinary cocycle to such a representative
is a separate obligation; no such reduction is assumed to be proved here. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_typeI_countable_matrix_closure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1 ∧
      FinitePathMain.TypeICentralSummand (1 : countableMatrixClosure e c) := by
  obtain ⟨c, hi, ho, ht⟩ := exists_countable_isometries e hno
  exact ⟨c, hi, ho, ht, countableMatrixClosure_typeI e c hi ho ht⟩

theorem primitive_of_countableMatrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver (countableMatrixClosure e c) f)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  obtain ⟨P⟩ := exists_rightModuleAveragingProjection e hno
  apply primitive_of_multimodular_columns P f hf _ hcocycle
  intro m
  exact countableMatrixClosure_columns e c hi ho ht (m + 1)

end BoundedHochschild.KadisonRingrose

end

end OAI
