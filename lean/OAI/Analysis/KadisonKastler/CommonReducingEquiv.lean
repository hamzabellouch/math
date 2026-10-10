import OAI.Analysis.KadisonKastler.ReducingFactorEquiv

namespace OAI

/-! # The same concrete subalgebra after faithful reducing restrictions -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem reducingAlgebra_mono {R M : VonNeumannAlgebra H} (hRM : R ≤ M)
    (hER : E.starProjection ∈ R.commutant) (hEM : E.starProjection ∈ M.commutant) :
    generatedVonNeumannAlgebra (commutantReducingHom E R hER).range ≤
      generatedVonNeumannAlgebra (commutantReducingHom E M hEM).range := by
  apply generatedVonNeumannAlgebra_le_of_le
  rintro T ⟨r, rfl⟩
  exact subset_generatedVonNeumannAlgebra _ ⟨coordinateInclusion hRM r, rfl⟩

theorem commutantReducingHom_injective_of_inclusion
    {R M : VonNeumannAlgebra H} (hRM : R ≤ M)
    (hER : E.starProjection ∈ R.commutant) (hEM : E.starProjection ∈ M.commutant)
    (hfaith : Function.Injective (commutantReducingHom E M hEM)) :
    Function.Injective (commutantReducingHom E R hER) := by
  intro a b hab
  have hi : coordinateInclusion hRM a = coordinateInclusion hRM b := hfaith hab
  exact Subtype.ext (congrArg (fun x : Algebra M => x.val) hi)

variable (R M : VonNeumannAlgebra H) (hRM : R ≤ M)
  (hER : E.starProjection ∈ R.commutant) (hEM : E.starProjection ∈ M.commutant)
  (hfaith : Function.Injective (commutantReducingHom E M hEM))

def reducingSubalgebraEquiv : Algebra R ≃⋆ₐ[ℂ]
    Algebra (generatedVonNeumannAlgebra (commutantReducingHom E R hER).range) :=
  boundedWeakNormalEquiv R (commutantReducingHom E R hER)
    (commutantReducingHom_injective_of_inclusion E hRM hER hEM hfaith)
    (commutantReducingHom_boundedWeakNormal E R hER)

theorem reducingSubalgebraEquiv_apply (r : Algebra R) :
    (reducingSubalgebraEquiv E R M hRM hER hEM hfaith r).val =
      cornerCompression E r.val := rfl

theorem reducingSubalgebraEquiv_restrict
    (P : VonNeumannAlgebra E)
    (hP : generatedVonNeumannAlgebra (commutantReducingHom E M hEM).range ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P)
    (he : ∀ a, (e a).val = cornerCompression E a.val) (r : Algebra R) :
    e (coordinateInclusion hRM r) =
      coordinateInclusion ((reducingAlgebra_mono E hRM hER hEM).trans hP)
        (reducingSubalgebraEquiv E R M hRM hER hEM hfaith r) := by
  apply Subtype.ext
  exact he (coordinateInclusion hRM r)

end

end KadisonKastler

end OAI
