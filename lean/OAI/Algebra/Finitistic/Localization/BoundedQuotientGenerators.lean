import OAI.Algebra.Finitistic.Localization.LocalizedEvaluationStructure

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy ThickEvaluation
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual degree-zero right vertex projective in K. -/
def vertexK (i : Fin 3) : BoundedK P :=
  ⟨(HomotopyCategory.quotient _ _).obj ((degreeZero P).obj (vertexModule P i)),
    single_property (vertexModule P i) 0⟩

def arrowK01 (h : Fin (d+1)) : vertexK P 0 ⟶ vertexK P 1 :=
  (inclusion (B P)ᵐᵒᵖ).preimage
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P h)))
def arrowK12 (h : Fin (d+1)) : vertexK P 1 ⟶ vertexK P 2 :=
  (inclusion (B P)ᵐᵒᵖ).preimage
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P h)))

theorem s_denominator : boundedDenominators P (arrowK01 P 0) := by
  obtain ⟨Z,g,h,hT⟩ := distinguished_cocone_triangle (arrowK01 P 0)
  let I := inclusion (B P)ᵐᵒᵖ
  have e : I.obj Z ≅ I.obj (boundedConeS P) :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _ (I.map_distinguished _ hT)
      (HomotopyCategory.mappingCone_triangleh_distinguished
        ((degreeZero P).map (arrowModule01 P 0))) (Iso.refl _) (Iso.refl _) (by
          change I.map (arrowK01 P 0) ≫ 𝟙 _ = 𝟙 _ ≫
            (HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P 0))
          unfold arrowK01
          erw [Functor.map_preimage]
          simp
          exact Category.comp_id _))
  have eK : Z ≅ boundedConeS P := I.preimageIso e
  exact ⟨Z,g,h,hT,Thick.iso eK.symm (Thick.generator (Or.inl rfl))⟩

instance quotient_s_isIso : IsIso ((boundedDenominators P).Q.map (arrowK01 P 0)) :=
  Localization.inverts (boundedDenominators P).Q (boundedDenominators P) _ (s_denominator P)

theorem s'_denominator : boundedDenominators P (arrowK12 P 0) := by
  obtain ⟨Z,g,h,hT⟩ := distinguished_cocone_triangle (arrowK12 P 0)
  let I := inclusion (B P)ᵐᵒᵖ
  have e : I.obj Z ≅ I.obj (boundedConeS' P) :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _ (I.map_distinguished _ hT)
      (HomotopyCategory.mappingCone_triangleh_distinguished
        ((degreeZero P).map (arrowModule12 P 0))) (Iso.refl _) (Iso.refl _) (by
          change I.map (arrowK12 P 0) ≫ 𝟙 _ = 𝟙 _ ≫
            (HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P 0))
          unfold arrowK12
          erw [Functor.map_preimage]
          simp
          exact Category.comp_id _))
  have eK : Z ≅ boundedConeS' P := I.preimageIso e
  exact ⟨Z,g,h,hT,Thick.iso eK.symm (Thick.generator (Or.inr rfl))⟩

instance quotient_s'_isIso : IsIso ((boundedDenominators P).Q.map (arrowK12 P 0)) :=
  Localization.inverts (boundedDenominators P).Q (boundedDenominators P) _ (s'_denominator P)

/-- The three actual images in the fixed quotient. -/
def vertexQ (i : Fin 3) : BoundedQ P := (boundedDenominators P).Q.obj (vertexK P i)
def arrowQ01 (h : Fin (d+1)) : vertexQ P 0 ⟶ vertexQ P 1 :=
  (boundedDenominators P).Q.map (arrowK01 P h)
def arrowQ12 (h : Fin (d+1)) : vertexQ P 1 ⟶ vertexQ P 2 :=
  (boundedDenominators P).Q.map (arrowK12 P h)

instance arrowQ01_zero_isIso : IsIso (arrowQ01 P 0) := quotient_s_isIso P
instance arrowQ12_zero_isIso : IsIso (arrowQ12 P 0) := quotient_s'_isIso P

/-- The normalized generator s^{-1} a_h on L=E_0 in Q. -/
def normalizedGenerator (h : Fin d) : End (vertexQ P 0) :=
  arrowQ01 P h.succ ≫ inv (arrowQ01 P 0)
end LittleFinitistic.QuadraticEncoding

end

end OAI
