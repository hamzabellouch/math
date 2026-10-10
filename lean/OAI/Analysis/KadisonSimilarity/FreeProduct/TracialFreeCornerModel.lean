import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialFreeCornerTheorem
import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedWordDensity
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralWordAlgebra

namespace OAI

/-! The remaining word and reflection data in the free-corner argument are
constructed from the local published reduced-product model and ordinary
generated-algebra density. In particular neither an invariant word
decomposition nor freeness of the compressed factors is an input. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {P : Type u} [CStarAlgebra P]

/-- The canonical half projection of a selfadjoint involution. -/
theorem symmetryHalfProjectionProof {D : StarSubalgebra ℂ P} (d : D)
    (hdstar : star d = d) (hdsq : d * d = 1) :
    IsStarProjection (dihedralHalfProjection
      (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) := by
  apply isStarProjection_dihedralHalfProjection
  · exact congrArg (fun x : D => (x : P)) hdstar
  · apply Units.ext
    exact congrArg (fun x : D => (x : P)) hdsq

/-- The half projection belongs to every star subalgebra containing its
reflection. -/
theorem symmetryHalfProjection_mem (C : StarSubalgebra ℂ P)
    {D : StarSubalgebra ℂ P} (d : D) (hdsq : d * d = 1) (hdC : (d : P) ∈ C) :
    dihedralHalfProjection
      (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C :=
  C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2 : ℂ)

/-- All integer rotations lie in a star subalgebra containing both
involutions. The inverse is the product in reverse order. -/
theorem symmetryRotation_zpow_mem (C : StarSubalgebra ℂ P)
    {D A : StarSubalgebra ℂ P} (d : D) (s : A)
    (hdsq : d * d = 1) (hssq : s * s = 1)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C) (j : ℤ) :
    (↑((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq) *
      symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) ^ j) : P) ∈ C := by
  cases j with
  | ofNat n =>
    have h : ((d : P) * (s : P)) ^ n ∈ C := C.pow_mem (C.mul_mem hdC hsC) n
    simpa only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul,
      symmetryUnit_coe] using h
  | negSucc n =>
    have h : ((s : P) * (d : P)) ^ (n + 1) ∈ C := C.pow_mem (C.mul_mem hsC hdC) (n + 1)
    simpa only [zpow_negSucc, ← inv_pow, mul_inv_rev, symmetryUnit_inv,
      Units.val_pow_eq_pow_val, Units.val_mul, symmetryUnit_coe] using h

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (words : RicardXuWordDecompositionInput G A D)
  (creation : RicardXuCreationInput G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
  (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P)
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

include hgen hfaithful hext S hsize hτ hf words creation ha htrace hhaar support
  comparison hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation in
/-- The free-corner estimate from the local reduced-product model. Word
coordinates, reduced density, the half projection, rotation membership and
compressed freeness are all derived. -/
theorem free_corner_of_published_local_models
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (K : StarSubalgebra ℂ (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))
    [IsClosed (K : Set (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))]
    (hK : (factorAlgebra
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property))
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC))).topologicalClosure = K)
    (compression : RicardXuCompressionInput
      ((G.halfCornerGeometry dU (symmetryHalfProjectionProof d hdstar hdsq)
        (trace_dihedralHalfProjection G.trace hτ dU hd0)).baseGeometry K)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property)).comap K.subtype)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC)).comap K.subtype))
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCR : C ≤ R) (hDR : D ≤ R)
    (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hCdense : ∀ x, x ∈ C → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure)
    (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
    (spectral : DihedralSpectralArcInput G.trace C (dU * sU) dU)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  have hdense := G.reducedWordGenerated_of_factorsTraciallyGenerate A D hτ hgen
  obtain ⟨U, hword⟩ := words hτ hfaithful hf hdense
  have hfree := G.scalarFree_corner_of_generated_word_density D A C hf hτ dU sU
    d.property s.property hd0 hs0 (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
    (symmetryHalfProjectionProof d hdstar hdsq)
    (symmetryHalfProjection_mem C d hdsq hdC) (fun x hx => hCdense (x : P) hx)
  exact G.free_corner_original_operator A D M hgen hfaithful hext S hsize U hword hτ
    creation hf hdense z ha htrace hhaar τ support comparison d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte hqe hN₀ frame hframe hsum published commutation C R
    (symmetryHalfProjectionProof d hdstar hdsq)
    (symmetryHalfProjection_mem D d hdsq d.property)
    (symmetryHalfProjection_mem C d hdsq hdC)
    (trace_dihedralHalfProjection G.trace hτ dU hd0) K hK compression E EC hCR hDR
    hdC hsC hRdense (symmetryRotation_zpow_mem C d s hdsq hssq hdC hsC)
    hfree hep hpe spectral T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
