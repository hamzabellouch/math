import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCornerApplication
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCompressionDischarge
import OAI.Analysis.KadisonSimilarity.FreeProduct.NormalFreeDihedral
import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialExpectations
import OAI.Analysis.KadisonSimilarity.Tracial.TracialGeometrySupport
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixExtension
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCommutationDischarge

namespace OAI

/-! The exact remaining published premises for one local free-product
application. Every field concerns the underlying tracial algebras or their
standard Hilbert models; none is an estimate for the operator being tested.
The generated algebras, frame, reflection and ordinary word density
provide the geometric data. -/

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
  (s : A) (hssq : s * s = 1)
  (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)

/-- Published local ingredients, specialized to the chosen small corner
and test symmetry. The applicability to the actual finite normal free
product is kept explicit in the finite-factor assembly. -/
structure LocalFreeCornerPublishedInputs : Prop where
  /-- Blackadar III.1.1.11: finite-factor projection comparison. -/
  comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re)

include M hτ hssq hfaithful in
/-- The local conclusion is derived from the published premises and the
actual small frame, for every commuting operator with its concrete corner
bound. No operator-estimate field occurs in the published bundle. -/
theorem free_corner_from_local_published_inputs
    (published : G.LocalFreeCornerPublishedInputs)
    (baseExpectation : Nonempty (TracialExpectation G.trace A))
    (hnormal : ∃ N : VonNeumannAlgebra H, G.left.range = N.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D)
    (S : RealTracialSequence (G.baseGeometry D).trace)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hf : ScalarFree G.trace D A)
    (hsstar : star s = s) (hs0 : G.trace (s : P) = 0)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨E⟩ := baseExpectation
  obtain ⟨N, hN⟩ := hnormal
  obtain ⟨EC⟩ := G.l2Generated_tracialExpectation hτ hfaithful N hN
    (StarAlgebra.adjoin ℂ ({(Q.half.reflection : P), (s : P)} : Set P))
  have spectral := G.generated_dihedral_spectralInput hτ hfaithful N hN D A hf
    (symmetryUnit (Q.half.reflection : P)
      (congrArg (fun x : D => (x : P)) Q.half.reflection_square))
    (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))
    Q.half.reflection.property s.property (Q.half.reflection_trace hτ) hs0
    (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) Q.half.reflection_star))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
  have support := G.rightSupportInput_of_normal_range hfaithful N hN
    (Q.frame.corner : P) (Q.frame.corner_projection.map D.subtype) A
  have matrixExtension := fun j => G.matrixConjugationExtensionInput_of_normal_range
    A D (M.embedding j) hτ hf hgen hfaithful N hN
  have commutation := G.tracialCommutationInput_of_normal_range hτ hfaithful N hN
  have hcompression := G.smallFrameCompressionInput_proved A D Q s hτ
  exact G.free_corner_from_smallFrame A D M Q s hsstar hssq hgen hfaithful
    matrixExtension S hsize hτ hf (ricardXuWordDecompositionInput G A D)
    (ricardXuCreationInput G A D) support published.comparison publishedDerivationInputs
    commutation hcompression E EC spectral hs0 T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
