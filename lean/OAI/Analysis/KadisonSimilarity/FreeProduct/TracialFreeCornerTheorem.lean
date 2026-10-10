import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialFreeCornerEstimate
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixSymmetrization
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSpectralTest

namespace OAI

/-! The tracial free-corner argument assembled from the actual word model,
matrix symmetrization, and spectral test. All propagation, Fourier-matrix,
operator-norm, and averaging conclusions are derived from the local inputs.
Only the underlying local model and the specified published inputs remain. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- An arbitrarily small positive spectral arc is available by choosing
the finite compression size. -/
theorem exists_arcWidth_le {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, 0 < N ∧ 4 * arcWidth N ≤ 2 * t := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  have heq : 4 * arcWidth (n + 1) = 2 * (1 / (n + 1 : ℝ)) := by
    have hnne : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold arcWidth
    push_cast
    field_simp [hnne]
    ring
  rw [heq]
  linarith

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

local instance assembledMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance assembledMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
  (hdense : ReducedWordGenerated G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

variable (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P) (show IsStarProjection (e : P) from ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq, congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩)))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]
  (hp : IsStarProjection (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))))
  (hpD : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ D)
  (hpC : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C)
  (htp : G.trace (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (1 / 2 : ℂ))

variable (K : StarSubalgebra ℂ (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))
  [IsClosed (K : Set (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))]
  (hK : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC)).topologicalClosure = K)
  (compression : RicardXuCompressionInput ((G.halfCornerGeometry (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) hp htp).baseGeometry K)
    ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD).comap K.subtype) ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC).comap K.subtype))
  (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
  (hCR : C ≤ R) (hDR : D ≤ R)
  (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
  (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
    (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
  (hpower : ∀ j : ℤ, (↑(((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) ^ j) : P) ∈ C)
  (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp G.trace) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC))
  (hep : (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) * (e : P) = (e : P)) (hpe : (e : P) * (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (e : P))
  (spectral : DihedralSpectralArcInput G.trace C ((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)))

include hgen hext S hsize hword hτ creation hf hdense ha htrace hhaar support comparison
  hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation
  hK compression E EC hCR hDR hfaithful hdC hsC hRdense hpower hfree hep hpe spectral in
/-- For an operator with the finite matrix symmetries, the actual spectral
test and the proved propagation give the uniform free-corner bound. -/
theorem free_corner_from_local_models (Y : H →L[ℂ] H)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (hYU : ∀ j w, Y.comp
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D Y t ε) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨N, hN, hwidth⟩ := exists_arcWidth_le ht
  have hπ : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  obtain ⟨F⟩ := spectral (arcWidth N) (arcWidth_pos hN).le hπ
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  have hcorner_e := hcorner (e : P) heP e.property hte
  obtain ⟨T, hT, hcomm, hFourier⟩ :=
    G.exists_actual_spectral_test A D C R hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte hp hpD hpC htp K hK compression E EC hCR hDR hfaithful hdC hsC
      hRdense hpower hfree hep hpe hN F hwidth Y hcorner_e
  exact G.free_corner_estimate_of_published_words A D M hgen hfaithful hext S hsize U hword hτ
    Y hYD hYU creation hf hdense z ha htrace hhaar τ support (e : P) heP e.property
    hqe comparison hN₀ frame hframe hsum hε hcorner_e published commutation d s e
    hdstar hdsq hd0 hsstar hssq hs0 he ht hte T hN
    (fun i j => realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)))
    (mul_pos (by norm_num) ht) hT hcomm hFourier

include hgen hext S hsize hword hτ creation hf hdense ha htrace hhaar support comparison
  hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation
  hK compression E EC hCR hDR hfaithful hdC hsC hRdense hpower hfree hep hpe spectral in
/-- The original operator satisfies the free-corner estimate. The extra
matrix symmetries are constructed by actual normalized Haar averaging, and
its exact base compression is restored at the end. -/
theorem free_corner_original_operator (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨Y, _hYnorm, hYD, hYU, hYcorner, hbase⟩ :=
    G.exists_tracially_symmetrized A D M hgen hfaithful hext T hTD hε hcorner
  rw [G.baseOperator_commutator_subalgebra A T s, ← hbase]
  exact G.free_corner_from_local_models A D M hgen hfaithful hext S hsize U hword hτ
    creation hf hdense z ha htrace hhaar τ support comparison d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte hqe hN₀ frame hframe hsum published commutation C R hp hpD hpC
    htp K hK compression E EC hCR hDR hdC hsC hRdense hpower hfree hep hpe spectral
    Y hYD hYU hε hYcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
