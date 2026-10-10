import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialEmbeddedWordStructure
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialHaarWordColumns
import OAI.Analysis.KadisonSimilarity.Tracial.TracialAdjointBounds
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialDihedralEndgame

namespace OAI

/-! The actual tracial word model supplies both errors in the Fourier
compression argument. The only remaining Fourier hypotheses below concern
the spectral test operator itself; level preservation and propagation are
derived from the matrix symmetries and the cited published inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v

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

local instance freeCornerMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance freeCornerMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (Y : H →L[ℂ] H)
  (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
  (hYU : ∀ j w, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)

include S hsize hword hτ hYD hYU in
/-- Both the operator and its adjoint preserve the actual word levels.
Star closure supplies the second conclusion; it is not additional data. -/
theorem tracial_word_level_ranges :
    (∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) ∧
    (∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) := by
  have hYL j a : Y.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y := hYD (M.embedding j a)
  have hYLstar j a : Y.adjoint.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y.adjoint :=
    G.adjoint_commutes_with_base D Y hYD (M.embedding j a)
  have hYUstar j w : Y.adjoint.comp
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp
        Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    have hs :
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w :
          H →L[ℂ] H).adjoint =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w⁻¹ :
          H →L[ℂ] H) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star,
        Unitary.star_eq_inv, map_inv]
    rw [hs]
    exact hYU j w⁻¹
  constructor
  · intro n x
    refine ⟨U.block Y n n x, ?_⟩
    exact (congrArg (fun T => T x)
      (G.tracial_word_levels_preserved A D M hgen hfaithful hext S hsize U hword hτ
        Y hYL hYU n)).symm
  · intro n x
    refine ⟨U.block Y.adjoint n n x, ?_⟩
    exact (congrArg (fun T => T x)
      (G.tracial_word_levels_preserved A D M hgen hfaithful hext S hsize U hword hτ
        Y.adjoint hYLstar hYUstar n)).symm

include S hsize hword hτ hYD hYU in
/-- The free-corner estimate with all word-structure and propagation
prerequisites derived. The published derivation inputs, the
elementary reduced creation model, and the standard support/comparison data
are explicit. The spectral test is used only through its norm and exact
finite Fourier compression. -/
theorem free_corner_estimate_of_published_words
    (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
    (hdense : ReducedWordGenerated G A D)
    {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
    (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e₀ : P) (he₀ : IsStarProjection e₀) (he₀D : e₀ ∈ D)
    (hqe : τ (q : P) ≤ τ e₀) (comparison : FiniteFactorProjectionComparison τ)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e₀ else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ x : CStarCorner e₀ he₀,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e₀ he₀))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (T : H →L[ℂ] H) {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {b : ℝ} (hb : 0 < b) (hT : ‖T‖ ≤ 3 * b)
    (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (b : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  let B := G.tracialWordRepeatedOperator A D M S hsize U Y
  have hYL j a : Y.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y := hYD (M.embedding j a)
  have hY := G.tracial_repeated_word A D M hgen hfaithful hext S hsize U hword hτ
    Y hYL hYU
  have hYstar := G.tracial_adjoint_repeated_word A D M hgen hfaithful hext S hsize U hword hτ
    Y hYL hYU
  have hlevels := G.tracial_word_level_ranges A D M hgen hfaithful hext S hsize U hword hτ
    Y hYD hYU
  have hprop := G.all_degrees_propagation_of_published_words A D hτ U z ha htrace hhaar
    hword creation hf hfaithful hdense s hs0 hsstar hssq Y hYD B hY
    τ support e₀ he₀ he₀D hqe comparison hN₀ frame hframe hsum hε hcorner published commutation
  have hpropstar := G.all_degrees_propagation_of_published_words A D hτ U z ha htrace hhaar
    hword creation hf hfaithful hdense s hs0 hsstar hssq Y.adjoint
    (G.adjoint_commutes_with_base D Y hYD) (fun n => (B n).adjoint) hYstar
    τ support e₀ he₀ he₀D hqe comparison hN₀ frame hframe hsum hε
    (G.adjoint_corner_commutator_bound e₀ he₀ Y hcorner) published commutation
  apply G.commutator_bound_of_actual_dihedral_compression A D hτ hf d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte U hword Y T B hY hYstar hlevels.1 hlevels.2 hN toeplitz
    hb hε cyclicConstant_pos.le hT hcomm hprop
  · simpa only [G.baseOperator_adjoint] using hpropstar
  · exact hfourier

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
