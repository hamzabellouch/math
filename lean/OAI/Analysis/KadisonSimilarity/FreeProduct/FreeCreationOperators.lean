import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeHeadCoordinates
import OAI.Analysis.KadisonSimilarity.FreeProduct.LeadingWordGeometry

namespace OAI

/-! Centered-letter creation maps on the actual leading-word subspaces. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D B : StarSubalgebra ℂ P)
  [IsClosed (B : Set P)] (side : Bool) (hB : B = if side then A else D)

abbrev FreeCreationParameter := CenteredTracialLetter G B × CenteredWordParameter G A D (!side)

def freeCreationTensor (p : FreeCreationParameter G A D B side) :
    HilbertTensor (centeredSubspace (G.baseVector B 1)) (centeredWordSpace G A D (!side)) :=
  hilbertTensorInsert (centeredLetterVector G B p.1)
    (closedFamilyVector (centeredWordFamily G A D (!side)) p.2)

def freeCreationVector (p : FreeCreationParameter G A D B side) : H :=
  G.vector ((p.1.1 : P) * p.2.1.prod)

theorem freeCreationTensor_total (hτ : G.trace 1 = 1) :
    (Submodule.span ℂ (Set.range (freeCreationTensor G A D B side))).topologicalClosure = ⊤ := by
  apply tensorFamily_total (centeredLetterVector G B)
    (closedFamilyVector (centeredWordFamily G A D (!side)))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mp
      ((centeredLetterVector_dense G B hτ).mono Submodule.subset_span)
  · exact closedFamilyVector_total _

include hB

theorem freeCreationGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (p q : FreeCreationParameter G A D B side) :
    inner ℂ (freeCreationVector G A D B side p) (freeCreationVector G A D B side q) =
      inner ℂ (freeCreationTensor G A D B side p) (freeCreationTensor G A D B side q) := by
  have hp : (p.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact p.1.1.property
  have hq : (q.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact q.1.1.property
  have ht : inner ℂ (freeCreationTensor G A D B side p) (freeCreationTensor G A D B side q) =
      G.trace (star (p.1.1 : P) * (q.1.1 : P)) *
        G.trace (star p.2.1.prod * q.2.1.prod) := by
    exact (inner_hilbertTensorInsert _ _ _ _).trans
      (congrArg₂ (· * ·) (G.baseVector_inner B p.1.1 q.1.1) (G.inner_vector _ _))
  rw [ht, freeCreationVector, freeCreationVector, G.inner_vector]
  exact hf.trace_matching_heads G.trace_star hτ hp hq p.2.2 q.2.2

def freeCreationIsometry (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D) :
    HilbertTensor (centeredSubspace (G.baseVector B 1))
      (centeredWordSpace G A D (!side)) →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (freeCreationTensor G A D B side) (freeCreationVector G A D B side)
    (freeCreationTensor_total G A D B side hτ) (freeCreationGram G A D B side hB hτ hf)

@[simp] theorem freeCreationIsometry_tensor (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (p : FreeCreationParameter G A D B side) :
    freeCreationIsometry G A D B side hB hτ hf (freeCreationTensor G A D B side p) =
      freeCreationVector G A D B side p := by
  unfold freeCreationIsometry
  exact denseFamilyIsometry_apply (freeCreationTensor G A D B side)
    (freeCreationVector G A D B side) (freeCreationTensor_total G A D B side hτ)
    (freeCreationGram G A D B side hB hτ hf) p

theorem freeCreationIsometry_mem (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (z : HilbertTensor (centeredSubspace (G.baseVector B 1))
      (centeredWordSpace G A D (!side))) :
    freeCreationIsometry G A D B side hB hτ hf z ∈ leadingWordSpace G A D side := by
  apply map_mem_of_total (freeCreationTensor G A D B side)
    (freeCreationTensor_total G A D B side hτ)
    (freeCreationIsometry G A D B side hB hτ hf).toContinuousLinearMap
  intro p
  change freeCreationIsometry G A D B side hB hτ hf (freeCreationTensor G A D B side p) ∈
    leadingWordSpace G A D side
  rw [freeCreationIsometry_tensor]
  have hp : (p.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact p.1.1.property
  have hx := AlternatingCenteredWord.cons hp p.1.2 p.2.2
  exact (closedFamilyVector (leadingWordFamily G A D side)
    ⟨⟨(p.1.1 : P) :: p.2.1, hx⟩, List.cons_ne_nil _ _⟩).property

theorem freeCreationIsometry_left (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (a : B) (ha : G.trace (a : P) = 0) (y : centeredWordSpace G A D (!side)) :
    freeCreationIsometry G A D B side hB hτ hf
      (hilbertTensorInsert (G.baseSymmetryLetter B a ha) y) = G.left (a : P) (y : H) := by
  let f := (freeCreationIsometry G A D B side hB hτ hf).toContinuousLinearMap.comp
      (hilbertTensorInsert (G.baseSymmetryLetter B a ha)) -
    (G.left (a : P)).comp (centeredWordSpace G A D (!side)).subtypeL
  have he : f = 0 := continuousLinearMap_eq_zero_of_total
    (closedFamilyVector (centeredWordFamily G A D (!side))) (closedFamilyVector_total _) f (by
      intro xs
      change freeCreationIsometry G A D B side hB hτ hf
          (freeCreationTensor G A D B side (⟨a, ha⟩, xs)) -
        G.left (a : P) (G.vector xs.1.prod) = 0
      rw [freeCreationIsometry_tensor, freeCreationVector, G.left_vector, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f y) he)

end KadisonSimilarity

end

end OAI
