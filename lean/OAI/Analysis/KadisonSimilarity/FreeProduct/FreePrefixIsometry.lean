import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeLeadingWords

namespace OAI

/-! A full first-factor letter tensored with opposite-factor words acts by
actual left multiplication. This constructs the head coordinates. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def freeHeadTensor (p : D × CenteredWordParameter G A D true) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) :=
  hilbertTensorInsert (G.baseVector D p.1)
    (closedFamilyVector (centeredWordFamily G A D true) p.2)

def freeHeadVector (p : D × CenteredWordParameter G A D true) : H :=
  G.vector ((p.1 : P) * p.2.1.prod)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadTensor_total :
    (Submodule.span ℂ (Set.range (freeHeadTensor G A D))).topologicalClosure = ⊤ := by
  apply tensorFamily_total (G.baseVector D) (closedFamilyVector (centeredWordFamily G A D true))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mp
      ((G.baseVector_dense D).mono (Submodule.subset_span))
  · exact closedFamilyVector_total _

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (p q : D × CenteredWordParameter G A D true) :
    inner ℂ (freeHeadVector G A D p) (freeHeadVector G A D q) =
      inner ℂ (freeHeadTensor G A D p) (freeHeadTensor G A D q) := by
  have ht : inner ℂ (freeHeadTensor G A D p) (freeHeadTensor G A D q) =
      G.trace (star (p.1 : P) * q.1) * G.trace (star p.2.1.prod * q.2.1.prod) := by
    exact (inner_hilbertTensorInsert _ _ _ _).trans
      (congrArg₂ (· * ·) (G.baseVector_inner D p.1 q.1) (G.inner_vector _ _))
  rw [ht, freeHeadVector, freeHeadVector, G.inner_vector]
  exact hf.trace_matching_heads G.trace_star hτ (side := false)
    p.1.property q.1.property p.2.2 q.2.2

def freeHeadIsometry (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (freeHeadTensor G A D) (freeHeadVector G A D)
    (freeHeadTensor_total G A D) (freeHeadGram G A D hτ hf)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
@[simp] theorem freeHeadIsometry_tensor (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (p : D × CenteredWordParameter G A D true) :
    freeHeadIsometry G A D hτ hf (freeHeadTensor G A D p) = freeHeadVector G A D p := by
  unfold freeHeadIsometry
  exact denseFamilyIsometry_apply (freeHeadTensor G A D) (freeHeadVector G A D)
    (freeHeadTensor_total G A D) (freeHeadGram G A D hτ hf) p

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadIsometry_left (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (d : D) (y : centeredWordSpace G A D true) :
    freeHeadIsometry G A D hτ hf (hilbertTensorInsert (G.baseVector D d) y) =
      G.left (d : P) (y : H) := by
  let f := (freeHeadIsometry G A D hτ hf).toContinuousLinearMap.comp
    (hilbertTensorInsert (G.baseVector D d)) -
      (G.left (d : P)).comp (centeredWordSpace G A D true).subtypeL
  have he : f = 0 := continuousLinearMap_eq_zero_of_total
    (closedFamilyVector (centeredWordFamily G A D true)) (closedFamilyVector_total _) f (by
      intro xs
      change freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (d, xs)) -
        G.left (d : P) (G.vector xs.1.prod) = 0
      rw [freeHeadIsometry_tensor, freeHeadVector, G.left_vector, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f y) he)

end KadisonSimilarity

end

end OAI
