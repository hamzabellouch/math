import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.InjectiveGeneration
import OAI.Algebra.FinitisticAsymmetry.Triangular.Generation
import OAI.Algebra.FinitisticAsymmetry.Rickard.NonGeneration

namespace OAI

section
noncomputable section
open CategoryTheory
namespace LittleFinitistic.AsymmetryConstruction
universe u
variable {k A ι : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Nontrivial A] [Fintype ι]
variable (χ : Aᵐᵒᵖ →ₐ[k] (ι → k))
abbrev Lambda := (CummingsConstruction.T χ)ᵐᵒᵖ

lemma all_clauses
    (hχ : Function.Surjective χ)
    (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥)
    (hA : littleFinitisticDimension A = ⊤) :
    FiniteDimensional k (Lambda χ) ∧
      littleFinitisticDimension (Lambda χ) = ⊤ ∧
      bigFinitisticDimension (Lambda χ) = ⊤ ∧
      littleFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 ∧
      bigFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate (Lambda χ) ∧ InjectivesGenerate (Lambda χ)ᵐᵒᵖ := by
  classical
  let eA := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)
  have hinf : littleFinitisticDimension (Lambda χ) = ⊤ := by
    apply top_unique
    rw [← hA, ← littleFinitisticDimension_equivalence eA]
    exact TriangularConstruction.right_little_lower_bound _ _ _
  have hbig : bigFinitisticDimension (Lambda χ) = ⊤ :=
    top_unique (hinf ▸ littleFinitisticDimension_le_big (Lambda χ))
  let eT := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.opOp (CummingsConstruction.T χ))
  obtain ⟨hlz, hbz⟩ := CummingsConstruction.left_dimensions_zero χ hχ hnil
  have hlz' : littleFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 :=
    (littleFinitisticDimension_equivalence eT).trans hlz
  have hbz' : bigFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 :=
    (bigFinitisticDimension_equivalence eT).trans hbz
  refine ⟨inferInstance, hinf, hbig, hlz', hbz', ?_, ?_⟩
  · exact Rickard.not_injectivesGenerate_of_little_eq_top k hinf
  · exact (injectivesGenerate_equivalence eT).mpr
      (CummingsConstruction.injectivesGenerate χ hχ hnil)
end LittleFinitistic.AsymmetryConstruction

end
end

end OAI
