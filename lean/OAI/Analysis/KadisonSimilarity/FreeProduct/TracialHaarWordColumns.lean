import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordBase
import OAI.Analysis.KadisonSimilarity.FreeProduct.ConcreteRepeatedPropagation
import OAI.Analysis.KadisonSimilarity.FreeProduct.PublishedWordCreation
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordPropagationTransfer

namespace OAI

/-! The Haar test columns used in propagation are actual reduced-word
inclusions. Their isometry and product formula follow from the word model
and the normalized corner Haar letters. -/

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance haarMultiplicityNormedFamily :
    ∀ k, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) k) :=
  fun _ => inferInstance

local instance haarMultiplicityInnerFamily :
    ∀ k, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) k) :=
  fun _ => inferInstance

variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- Unit vacuum endpoint and unit centered Haar letters give isometric
columns at every word degree. -/
def haarRepeatedWordInclusion (k n : ℕ) : WordMultiplicity (G.baseVector A 1) k →ₗᵢ[ℂ] H :=
  repeatedWordInclusion U k (LinearIsometry.id :
    WordMultiplicity (G.baseVector A 1) k →ₗᵢ[ℂ] WordMultiplicity (G.baseVector A 1) k)
    (G.baseVector D 1) (G.baseHaarLetter D z ha htrace hhaar n)
    (G.norm_baseVector_one D hτ) (G.norm_baseHaarLetter D z ha htrace hhaar n)

include hτ z ha htrace hhaar

/-- On bounded base vectors this column is precisely the ordinary repeated
product, with no independently assumed prefix formula. -/
theorem haarRepeatedWordInclusion_baseVector
    (hU : TracialWordFormula G A D U)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (k n : ℕ) (b : A) :
    G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar k n
      (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b)) =
      G.vector (((s : P) * (haarCornerLetter z a n : D)) ^ k * (b : P)) := by
  have hx0 : G.trace (haarCornerLetter z a n : D) = 0 :=
    haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htrace hhaar n
  simpa only [haarRepeatedWordInclusion, repeatedWordInclusion_apply,
    LinearIsometry.id_apply, baseSymmetryRepeatedInclusion,
    repeatedMultiplicityInclusion_apply, tracialWordTensor, tracialMultiplicityWord,
    tracialEndpointWord, baseHaarLetter, baseSymmetryLetter,
    OneMemClass.coe_one, one_mul] using
      hU.repeated_word_formula k (1 : D) (haarCornerLetter z a n) s b hs0 hx0

/-- The final Haar letter is supported on q, so the product formula is the
exact small-column factorization consumed by propagation. -/
theorem haarRepeatedWordInclusion_factor
    (hU : TracialWordFormula G A D U)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (m n : ℕ) (b : A) :
    G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1) n
      (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
        (G.baseVector A b)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P)
          (G.vector ((q : P) * (b : P)))) := by
  rw [G.haarRepeatedWordInclusion_baseVector A D hτ U z ha htrace hhaar hU,
    G.left_vector, G.left_vector]
  have hxq : ((haarCornerLetter z a n : D) : P) * (q : P) =
      ((haarCornerLetter z a n : D) : P) :=
    congrArg (fun x : D => (x : P)) (haarCornerLetter_mul_support z a n)
  congr 1
  simp only [tracialWordPrefix, StarSubalgebra.subtype_apply, pow_succ, mul_assoc]
  rw [← mul_assoc ((haarCornerLetter z a n : D) : P) (q : P), hxq]

/-- The published elementary creation maps and the ordinary product formula
give the manuscript's propagation estimate. The test word columns and their
prefix identities are constructed here. -/
theorem repeated_propagation_of_published_words
    (hU : TracialWordFormula G A D U)
    (creation : RicardXuCreationInput G A D)
    (hf : ScalarFree G.trace D A) (hfaithful : Function.Injective G.vector)
    (hdense : ReducedWordGenerated G A D)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (m : ℕ) (Y : H →L[ℂ] H)
    (hbase : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (B : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (hY : ∀ v d r, Y (U.inclusion (m + 1)
        (hilbertTensorInsert v (endpointWord d (fun _ : Fin (m + 1) => r)))) =
      U.inclusion (m + 1) (hilbertTensorInsert (B v)
        (endpointWord d (fun _ : Fin (m + 1) => r))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (comparison : FiniteFactorProjectionComparison τ)
    {N : ℕ} (hN : 0 < N) (frame : Fin N → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖B (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1) v) -
      G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  obtain ⟨W⟩ := creation hτ hfaithful hf hdense
  let := W.head.vacuum_hasOrthogonalProjection (G.baseGeometry_trace_one D hτ)
  let C := W.tracialCreationFormulas s hs0 z ha htrace hhaar
  apply concrete_repeated_propagation G A D W.head s hs0 hsstar hssq z ha htrace hhaar C
    hf hτ m Y hbase hYD B
    (G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1))
    ?_ ?_ τ support e he heD hqe hfaithful comparison hN frame hframe hsum hε hcomm
    published commutation v
  · intro n w
    simpa only [haarRepeatedWordInclusion, repeatedWordInclusion_apply,
      LinearIsometry.id_apply] using
      hY (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1) w)
        (G.baseVector D 1) (G.baseHaarLetter D z ha htrace hhaar n)
  · exact G.haarRepeatedWordInclusion_factor A D hτ U z ha htrace hhaar hU
      s hs0 hsstar hssq m

/-- The degree-zero case is exact, and every positive degree follows from
the constructed Haar test columns. Base-space invariance is derived from
the same ordinary word action. -/
theorem all_degrees_propagation_of_published_words
    (hU : TracialWordFormula G A D U)
    (creation : RicardXuCreationInput G A D)
    (hf : ScalarFree G.trace D A) (hfaithful : Function.Injective G.vector)
    (hdense : ReducedWordGenerated G A D)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (Y : H →L[ℂ] H)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (B : ∀ k, WordMultiplicity (G.baseVector A 1) k →L[ℂ]
      WordMultiplicity (G.baseVector A 1) k)
    (hY : ∀ k v d r, Y (U.inclusion k
        (hilbertTensorInsert v (endpointWord d (fun _ : Fin k => r)))) =
      U.inclusion k (hilbertTensorInsert (B k v) (endpointWord d (fun _ : Fin k => r))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (comparison : FiniteFactorProjectionComparison τ)
    {N : ℕ} (hN : 0 < N) (frame : Fin N → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (k : ℕ) (v : G.baseSpace A) :
    ‖B k (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v) -
      G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  have hzero : ∀ w, Y (U.inclusion 0 (hilbertTensorInsert w
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (B 0 w)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1))) := by
    intro w
    have hz : (fun _ : Fin 0 => (0 : centeredSubspace (G.baseVector D 1))) = Fin.elim0 :=
      Subsingleton.elim _ _
    simpa only [emptyEndpoint, hz] using hY 0 w (G.baseVector D 1) 0
  have hbase := G.baseSpace_invariant_of_word_action A D hτ U hU Y (B 0) hzero
  cases k with
  | zero =>
    have hb := G.baseOperator_of_word_action A D hτ U hU Y (B 0) hzero
    simp only [baseSymmetryRepeatedInclusion, repeatedMultiplicityInclusion_zero, hb,
      LinearIsometryEquiv.coe_toLinearIsometry, zeroMultiplicityOperator_intertwines,
      sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) cyclicConstant_pos.le) hε)
      (norm_nonneg v)
  | succ k =>
    exact G.repeated_propagation_of_published_words A D hτ U z ha htrace hhaar hU
      creation hf hfaithful hdense s hs0 hsstar hssq k Y hbase hYD (B (k + 1)) (hY (k + 1))
      τ support e he heD hqe comparison hN frame hframe hsum hε hcomm published commutation v

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
