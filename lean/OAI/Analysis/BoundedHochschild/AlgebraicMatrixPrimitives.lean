import OAI.Analysis.BoundedHochschild.MultimodularNormalReduction

namespace OAI

/-! The properly infinite primitive endpoint needs module identities only
on the algebraic countable matrix units. Separate normality is supplied by
the proved normal reduction, retaining those identities. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem primitive_of_algebraic_matrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 2))
    (hM : MultimodularOver (countableMatrixAlgebra c) f)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  obtain ⟨F, b, hFN, hFM, hFc, hid⟩ :=
    normal_reduction_multimodular e (countableMatrixAlgebra c) f hf hM
  obtain ⟨g, _, hg⟩ := primitive_of_normal_matrix_multimodular e hno c hi ho ht F hFN hFM hFc
  refine ⟨g + b, fun x => ?_⟩
  rw [differentialValue_add, hg]
  exact (hid x).symm

theorem primitive_of_matrix_units [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 2))
    (hM : ∀ i j, MultimodularAt f (countableMatrixUnit c i j))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x :=
  primitive_of_algebraic_matrix_multimodular e hno c hi ho ht f
    (multimodular_of_matrixUnits c hi ho f hM) hf

end BoundedHochschild.KadisonRingrose

end

end OAI
