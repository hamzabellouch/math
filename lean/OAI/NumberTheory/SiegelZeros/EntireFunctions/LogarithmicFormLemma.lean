import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicForm

namespace OAI

namespace SiegelZeros

section
open WeightedTorusJets.Geometry

theorem WeightedTorusJets.Geometry.logarithmic_form_lemma_source
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c) :
    (∀ (P : Ideal (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))) (hP : P.IsPrime),
      letI := hP
      0 < ringKrullDim (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ) ⧸ P) →
      let A := AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ) ⧸ P
      let F := FractionRing A
      let x := fun i ↦ algebraMap _ F
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
      let T := LinearMap.range (logarithmicTangentMap (k := ℂ) x)
      logarithmicForm c x ≠ 0 ∧
      Module.finrank F (LinearMap.range
        (T.mkQ.domRestrict (LinearMap.ker (logarithmicLinearForm c)))) =
          4 - ((ringKrullDim A).unbotD 0).toNat) ∧
    ∀ y : Fin 4 → ℂˣ,
      Module.finrank ℂ (LinearMap.range
        ((LinearMap.range (logarithmicTangentMap (k := ℂ) (fun i ↦ (y i : ℂ)))).mkQ.domRestrict
          (LinearMap.ker (logarithmicLinearForm (F := ℂ) c)))) = 3 := by
  exact WeightedTorusJets.Geometry.logarithmic_form_lemma_exact (K := ℂ) c hc

end

end SiegelZeros

end OAI
