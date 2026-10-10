import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsIntegerSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Filter Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistoryBulkGiantIntegerReference PrimeCellFreezing

theorem selected_integer_corrected_integrals_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (k₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (_hblock : Real.exp ((1/20:ℝ)*L) ≤ C.blockBase)
    (_hcenter : C.blockBase-2 < (C.giantCenter:ℝ))
    (s : ℕ) (outside : List ℕ) (_houtside : ∀q∈outside,0<q) (_hout : outside.length=2*s)
    (l : ℕ) (_hl : l < k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (_hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (_hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (_he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (_hP : 0<P) (_hQ : 0<Q) (_hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (_hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1),
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T (permutedAssignment C l σ x) q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    let eB := integerOrderedEquiv C V l outside σ x p q P Q c e hs
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointCorrectedScalar C s h g hs gs (boolEquiv h g) eB)‖ ≤
        64*2^(2^l*(2*(bulkSize k₀ L/2)))*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointCorrectedScalar C s h g hs gs (optionEquiv h g) eB)‖ ≤
        64*2^(2^l*(2*(bulkSize k₀ L/2)))*mainAmplitude Bs k₀ L l := by
  filter_upwards [source_integralBounds_eventually d Bs BD Bz k₀] with L hI
  intro E C hblock hcenter s outside houtside hout l hl σ x p q P Q c e
    hx hc he hP hQ hPc hQc
  dsimp only
  intro hs gs
  have hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass
      (permutedAssignment C l σ x) ≠ 0 := by
    rw [permutedAssignment_mass]
    exact hx
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    reference_corrected_integrals_le C (hI E C hblock hcenter) s outside houtside hout l hl
      x (permutedAssignment C l σ x) p q P Q c e hx hy hc he hP hQ hPc hQc
      hs gs (integerMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q P Q c e)
      (Fin (2^l)×Fin (2*(bulkSize k₀ L/2)))
      (integerOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q P Q c e hs)

theorem selected_integer_plain_integrals_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (k₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
    (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (_hblock : Real.exp ((1/20:ℝ)*L) ≤ C.blockBase)
    (_hcenter : C.blockBase-2 < (C.giantCenter:ℝ))
    (s : ℕ) (outside : List ℕ) (_houtside : ∀q∈outside,0<q) (_hout : outside.length=2*s)
    (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (_hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (_hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (_he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (_hP : 0<P) (_hQ : 0<Q) (_hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (_hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1),
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T (permutedAssignment C l σ x) q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    let eB := integerOrderedEquiv C V l outside σ x p q P Q c e hs
    ‖nestedPrimeIntegral L C.giantCenter E
      (jointScalar C s h g hs gs (boolEquiv h g) eB)‖ ≤
        64*2^(2^l*(2*(bulkSize k₀ L/2)))*mainAmplitude Bs k₀ L l ∧
    ‖nestedMixedIntegral L C.giantCenter E
      (jointScalar C s h g hs gs (optionEquiv h g) eB)‖ ≤
        64*2^(2^l*(2*(bulkSize k₀ L/2)))*mainAmplitude Bs k₀ L l := by
  filter_upwards [source_integralBounds_eventually d Bs BD Bz k₀] with L hI
  intro E C hblock hcenter s outside houtside hout l  σ x p q P Q c e
    hx hc he hP hQ hPc hQc
  dsimp only
  intro hs gs
  have hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass
      (permutedAssignment C l σ x) ≠ 0 := by
    rw [permutedAssignment_mass]
    exact hx
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    reference_plain_integrals_le C (hI E C hblock hcenter) s outside houtside hout l 
      x (permutedAssignment C l σ x) p q P Q c e hx hy hc he hP hQ hPc hQc
      hs gs (integerMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q P Q c e)
      (Fin (2^l)×Fin (2*(bulkSize k₀ L/2)))
      (integerOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q P Q c e hs)

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
