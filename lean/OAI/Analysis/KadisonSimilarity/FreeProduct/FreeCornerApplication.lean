import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedDihedralAlgebras
import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerData
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCompressionDischarge

namespace OAI

/-! Apply the proved free-corner theorem using the chosen matrix frame,
its containing half projection, and the actual L²-generated test algebras.
All ordinary generation and support identities are derived here. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hsstar : star s = s) (hssq : s * s = 1)

local notation "d" => Q.half.reflection
local notation "dU" => symmetryUnit (d : P)
  (congrArg (fun x : D => (x : P)) Q.half.reflection_square)
local notation "p" => dihedralHalfProjection dU
local notation "hp" => symmetryHalfProjectionProof d Q.half.reflection_star
  Q.half.reflection_square
local notation "C" => G.generatedDihedralAlgebra (d : P) (s : P)
local notation "K" => StarSubalgebra.topologicalClosure (factorAlgebra
  (CStarCorner.subalgebra p hp D
    (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property))
  (CStarCorner.subalgebra p hp C
    (symmetryHalfProjection_mem C d Q.half.reflection_square
      (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))))

local instance smallFrameCorner_isClosed : IsClosed (K : Set (CStarCorner p hp)) :=
  StarSubalgebra.isClosed_topologicalClosure _

/-- The elementary compression model on the actual half corner. -/
def smallFrameCompressionInput (hτ : G.trace 1 = 1) : Prop :=
  RicardXuCompressionInput
    ((G.halfCornerGeometry dU hp (trace_dihedralHalfProjection G.trace hτ
      dU (Q.half.reflection_trace hτ))).baseGeometry K)
    ((CStarCorner.subalgebra p hp D
      (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property)).comap (K).subtype)
    ((CStarCorner.subalgebra p hp C
      (symmetryHalfProjection_mem C d Q.half.reflection_square
        (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))).comap (K).subtype)

omit [IsClosed (A : Set P)] in
/-- The constructed reduced-word model supplies the half-corner input. -/
theorem smallFrameCompressionInput_proved (hτ : G.trace 1 = 1) :
    G.smallFrameCompressionInput A D Q s hτ := by
  unfold smallFrameCompressionInput
  exact ricardXuCompressionInput _ _ _

include hsstar in
/-- The free-corner estimate with the matrix frame and both generated
algebras fixed by construction. The remaining premises are the local
published word, spectral, comparison, and cyclic-implementation inputs. -/
theorem free_corner_from_smallFrame
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
    (S : RealTracialSequence (G.baseGeometry D).trace)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (words : RicardXuWordDecompositionInput G A D)
    (creation : RicardXuCreationInput G A D)
    (support : TracialRightSupportInput (fun a => (G.trace a).re)
      (Q.frame.corner : P) A)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (published : PublishedDerivationInputs.{u,v} (CStarCorner (Q.frame.corner : P)
      ⟨congrArg (fun x : D => (x : P)) Q.frame.corner_projection.isIdempotentElem.eq,
        congrArg (fun x : D => (x : P)) Q.frame.corner_projection.isSelfAdjoint.star_eq⟩))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (compression : G.smallFrameCompressionInput A D Q s hτ)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (spectral : DihedralSpectralArcInput G.trace C
      (dU * symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) dU)
    (hs0 : G.trace (s : P) = 0)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  have hd0 : G.trace (d : P) = 0 := Q.half.reflection_trace hτ
  have hframe (i j : Fin Q.size) :
      star (Q.frame.column i : P) * (Q.frame.column j : P) =
        if i = j then (Q.frame.corner : P) else 0 := by
    change ((star (Q.frame.column i) * Q.frame.column j : D) : P) = _
    rw [Q.frame.initial]
    split_ifs <;> rfl
  have hsum : ∑ i, (Q.frame.column i : P) * star (Q.frame.column i : P) = 1 := by
    have h := congrArg D.subtype Q.frame.resolution
    simp only [map_sum, map_mul, map_star, map_one] at h
    convert h using 1
    rfl
  have hhalf : p = (Q.half.projection : P) := by
    have h := congrArg D.subtype Q.half.reflection_half
    change (1 / 2 : ℂ) • (1 + (d : P)) = (Q.half.projection : P) at h
    exact h
  have hpe : p * (Q.frame.corner : P) = (Q.frame.corner : P) := by
    rw [hhalf]
    exact congrArg D.subtype Q.half.left_support
  have hep : (Q.frame.corner : P) * p = (Q.frame.corner : P) := by
    rw [hhalf]
    exact congrArg D.subtype Q.half.right_support
  let R := G.generatedTestAlgebra D (s : P)
  exact G.free_corner_of_published_local_models A D M hgen hfaithful hext S hsize
    hτ hf words creation Q.haar Q.trace_pos Q.corner_trace Q.moments
    (fun a => (G.trace a).re) support comparison d s Q.frame.corner
    Q.half.reflection_star Q.half.reflection_square hd0 hsstar hssq hs0
    Q.frame.corner_projection Q.trace_pos Q.corner_trace (le_refl _) Q.size_pos
    Q.frame.column hframe hsum published commutation C R
    (G.first_mem_generatedDihedralAlgebra (d : P) (s : P))
    (G.second_mem_generatedDihedralAlgebra (d : P) (s : P))
    K rfl compression E EC
    (G.generatedDihedralAlgebra_le_test D d (s : P))
    (G.le_generatedTestAlgebra D (s : P))
    (fun x hx => G.generatedTestAlgebra_density D (s : P) ⟨x, hx⟩)
    (fun x hx => G.generatedDihedralAlgebra_density (d : P) (s : P) ⟨x, hx⟩)
    hpe hep spectral T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
