import OAI.Analysis.KadisonSimilarity.Tracial.TracialCreationCoordinates
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSmallColumn
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialPropagationEndgame

namespace OAI

/-! Repeated-word propagation with all small-vector and prefix estimates
constructed from the actual scalar-free tracial model. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} {F : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (W : TracialHeadCoordinates (G.baseGeometry D) G D.subtype F)
  [W.vacuum.HasOrthogonalProjection]
  (s : A) (hzero : G.trace (s : P) = 0)
  (hself : star s = s) (hsquare : s * s = 1)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  {ALead : Submodule ℂ H}
  (C : TracialCreationFormulas G A D W s hzero z ha htrace hhaar ALead)

include C ha htrace hhaar in
/-- The propagation conclusion for a positive degree. Only elementary word
formulas remain as geometric inputs: small-vector normalization, prefix
isometry, the exceptional coefficient limit, and the full-column estimate
are proved in the construction. -/
theorem concrete_repeated_propagation
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (m : ℕ) (Y : H →L[ℂ] H)
    (hbase : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (Bₖ : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (word : ℕ → WordMultiplicity (G.baseVector A 1) (m + 1) →ₗᵢ[ℂ] H)
    (hlevel : ∀ n v, Y (word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)) =
      word n (Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)))
    (hword : ∀ n (v : A), word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseVector A v)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P)
          (G.vector ((q : P) * (v : P)))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (hfaithful : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison τ)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x : CStarCorner e he,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v) -
      G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  let R := C.repeatedWordRealization hself hsquare hτ m Y (G.baseOperator A Y) Bₖ word
    (G.tracialSmallColumn A (q : P))
    (G.norm_tracialSmallColumn A D hf hτ (q : P) (hq.map D.subtype) q.property ha.le htrace)
    (G.tracialSmallColumn_level_zero A (q : P) Y hbase (hYD q)) hlevel
    (fun v => congrArg (fun T : G.baseSpace A →L[ℂ] H => T v)
      (G.tracialSmallColumn_support A (q : P) (hq.map D.subtype)))
    (by simpa only [G.tracialSmallColumn_vector] using hword)
  exact R.propagation_on_base_of_published_inputs
    (G.baseGeometry_trace_one D hτ) ha htrace hhaar τ support
    (G.tracialSmallColumn_vector A (q : P)) e he hqe
    hfaithful comparison hn (fun i => (frame i : P)) hframe hsum
    (hYD ⟨e, heD⟩) (fun i => hYD (frame i)) hε hY published commutation v

end KadisonSimilarity

end

end OAI
