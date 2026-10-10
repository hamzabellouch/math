import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixConjugationUnitary
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixBaseAction
import OAI.Analysis.KadisonSimilarity.Representation.NormalFactorGeneration

namespace OAI

/-! The matrix-factor automorphism extends to the actual normal tracial
algebra by conjugating its left representation with the free-word unitary. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (h1 : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : G.FactorsTraciallyGenerate A D)

def freeMatrixExtensionUnitary : H ≃ₗᵢ[ℂ] H :=
  G.freeMatrixConjugationUnitary A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen)

private theorem conjugate_eq_of_intertwining (U : H ≃ₗᵢ[ℂ] H)
    (T S : H →L[ℂ] H)
    (h : U.toLinearIsometry.toContinuousLinearMap.comp T =
      S.comp U.toLinearIsometry.toContinuousLinearMap) : U.conjStarAlgEquiv T = S := by
  ext ξ
  have hx := congrArg (fun F : H →L[ℂ] H => F (U.symm ξ)) h
  change U (T (U.symm ξ)) = S (U (U.symm ξ)) at hx
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simpa only [U.apply_symm_apply] using hx

local notation "U" => G.freeMatrixExtensionUnitary A D ι u h1 hf hgen

theorem freeMatrixExtensionUnitary_base (a : A) :
    (U).conjStarAlgEquiv (G.left (a : P)) = G.left (a : P) := by
  apply conjugate_eq_of_intertwining
  exact G.freeMatrixConjugationIsometry_base_left A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen) a

theorem freeMatrixExtensionUnitary_other (d : D) :
    (U).conjStarAlgEquiv (G.left (d : P)) =
      G.left (matrixConjugateLetter D ι u d : P) := by
  apply conjugate_eq_of_intertwining
  exact G.freeMatrixConjugationIsometry_other A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen) d

@[simp] theorem freeMatrixExtensionUnitary_one : U (G.vector 1) = G.vector 1 :=
  G.freeMatrixConjugationIsometry_one A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen)

def freeMatrixExtensionRepresentation : P →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (U).conjStarAlgEquiv.toStarAlgHom.comp G.left

@[simp] theorem freeMatrixExtensionRepresentation_apply (x : P) :
    G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x =
      (U).conjStarAlgEquiv (G.left x) := rfl

variable (hfaithful : Function.Injective G.vector) (M : VonNeumannAlgebra H)
  (hrange : G.left.range = M.toStarSubalgebra)

include hfaithful hrange in
theorem freeMatrixExtensionRepresentation_mem (x : P) :
    G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x ∈ M := by
  apply G.normal_range_map_mem A D h1 hfaithful M hrange hgen (U).conjStarAlgEquiv
  · intro a
    rw [G.freeMatrixExtensionUnitary_base A D ι u h1 hf hgen]
    change G.left (a : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(a : P), rfl⟩
  · intro d
    rw [G.freeMatrixExtensionUnitary_other A D ι u h1 hf hgen]
    change G.left (matrixConjugateLetter D ι u d : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(matrixConjugateLetter D ι u d : P), rfl⟩

/-- The algebraic extension in the original algebra, using its faithful normal coordinates. -/
def freeMatrixExtensionHom : P →⋆ₐ[ℂ] P :=
  (equivalenceOfConcreteRange M G.left (G.left_injective hfaithful)
    hrange).symm.toStarAlgHom.comp
      ((G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen).codRestrict
        M.toStarSubalgebra (G.freeMatrixExtensionRepresentation_mem A D ι u h1 hf hgen
          hfaithful M hrange))

theorem freeMatrixExtensionHom_left (x : P) :
    G.left (G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange x) =
      G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hfaithful)
    hrange
  let r := (G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen).codRestrict
    M.toStarSubalgebra (G.freeMatrixExtensionRepresentation_mem A D ι u h1 hf hgen
      hfaithful M hrange)
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H)) (e.apply_symm_apply (r x))

theorem freeMatrixExtensionHom_base (a : A) :
    G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange (a : P) = (a : P) := by
  apply G.left_injective hfaithful
  rw [G.freeMatrixExtensionHom_left, G.freeMatrixExtensionRepresentation_apply,
    G.freeMatrixExtensionUnitary_base]

theorem freeMatrixExtensionHom_other (d : D) :
    G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange (d : P) =
      (matrixConjugateLetter D ι u d : P) := by
  apply G.left_injective hfaithful
  rw [G.freeMatrixExtensionHom_left, G.freeMatrixExtensionRepresentation_apply,
    G.freeMatrixExtensionUnitary_other]

private theorem vectorTrace_conjugate (V : H ≃ₗᵢ[ℂ] H) (Ω : H) (hΩ : V Ω = Ω)
    (T : H →L[ℂ] H) : vectorTrace Ω (V.conjStarAlgEquiv T) = vectorTrace Ω T := by
  have hs : V.symm Ω = Ω := by
    apply V.injective
    rw [V.apply_symm_apply, hΩ]
  rw [vectorTrace_apply, vectorTrace_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
  calc
    inner ℂ Ω (V (T Ω)) = inner ℂ (V Ω) (V (T Ω)) := by rw [hΩ]
    _ = inner ℂ Ω (T Ω) := V.inner_map_map Ω (T Ω)

theorem freeMatrixExtensionHom_trace (x : P) :
    G.trace (G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange x) =
      G.trace x := by
  rw [← G.trace_eq_vectorTrace, G.freeMatrixExtensionHom_left,
    G.freeMatrixExtensionRepresentation_apply, ← G.trace_eq_vectorTrace x]
  exact vectorTrace_conjugate (U) (G.vector 1)
    (G.freeMatrixExtensionUnitary_one A D ι u h1 hf hgen) (G.left x)

include h1 hf hgen hfaithful M hrange in
/-- Blanchard--Dykema's two-factor extension specialization, constructed
for the given faithful normal tracial free product. -/
theorem matrixConjugationExtensionInput_of_normal_range :
    G.MatrixConjugationExtensionInput D ι A := by
  intro v
  exact ⟨G.freeMatrixExtensionHom A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_trace A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_base A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_other A D ι v h1 hf hgen hfaithful M hrange⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
