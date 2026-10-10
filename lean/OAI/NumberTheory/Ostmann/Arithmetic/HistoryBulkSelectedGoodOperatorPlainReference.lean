import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedGoodOperatorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementCorrectedPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsInteger

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkSelectedGoodOperator
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistorySelectedPairDerivativeBounds PrimeCellFreezing
open HistoryBulkPriorGrid HistoryPrincipalIntegralAverage HistoryBulkReplacementGeometry
open HistoryBulkGiantIntegerReference HistoryBulkResidueNormSum ScaleBudget Filter
open HistorySelectedJointIntegralBounds HistoryRepresentativeIntegerAdmissible
open HistoryBulkSelectedIntegralReplacement
open HistorySignedSpectatorDiagramAverage

theorem reference_plain_good_operator_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k₀ : ℕ} (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
    (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
      Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    (∀p : spectator.Sample, (FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ ε) →
    ∀ ds : Fin (2*(bulkSize k₀ L/2))→spectator.Sample,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
    Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
    C.blockBase-2 < (C.giantCenter:ℝ) →
    (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
    |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
    |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ (l : ℕ) (_hl : l ≤ k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (_hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (_hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y ≠ 0)
    (_hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (_he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (_hP : 0<P) (_hQ : 0<Q) (_hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (_hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1),
    let outside := spectatorList spectator ds
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    ∀ (_hmatch : RootMatching h g)
      (eB : (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))) ≃ bulkCoordinates h g),
    ∀ (hV : ∀r∈outside,∀j≤l,V j<r), ¬TransferBadArrangement σ →
    let N := bulkModulus h g outside k₀
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
    principalPayment Bs BD Bz L k₀ l *
      ‖nestedPrimeIntegral L C.giantCenter E
        (jointScalar C (bulkSize k₀ L/2) h g hs gs (boolEquiv h g) eB) *
          ResidueHaar.average (rootTest true false d h g hs gs (spectatorPrimes spectator ds) hV σ k₀)‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k₀ L:ℝ)) ∧
    principalPayment Bs BD Bz L k₀ l *
      ‖nestedMixedIntegral L C.giantCenter E
        (jointScalar C (bulkSize k₀ L/2) h g hs gs (optionEquiv h g) eB) *
          ResidueHaar.average (rootTest true true d h g hs gs (spectatorPrimes spectator ds) hV σ k₀)‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k₀ L:ℝ)) := by
  obtain ⟨ε,hε,hbudget⟩ := exists_rootTest_good_operator_budget d Bs BD Bz H hBs hk₀ hH
  refine ⟨ε,hε,?_⟩
  filter_upwards [hbudget,
    source_integralBounds_eventually d Bs BD Bz k₀,
    selected_integer_pair_admissible_eventually d Bs BD Bz hk₀,
    eventually_ge_atTop (0:ℝ)] with L hBudget hIntegral hAd hL0
  intro spectator hspec hflat ds E C hblock hcenter hupper hbulk hspectator
    l hl σ x y p q P Q c e hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs gs hmatch eB hV hgood
  have hmem : ∀r∈spectatorList spectator ds,r∈spectator.candidates := by
    intro r hr
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hr
    rw [← hi]
    exact (ds i).property
  have hlen : (spectatorList spectator ds).length = bulkSize k₀ L := by
    simp only [spectatorList,List.length_ofFn]
    unfold bulkSize
    omega
  have hout : (spectatorList spectator ds).length = 2*(bulkSize k₀ L/2) := by
    simp only [spectatorList,List.length_ofFn]
  have hthree : ∀r∈spectatorList spectator ds,3≤r := by
    intro r hr
    exact spectator_three_le hL0 r (spectator.prime r (hmem r hr))
      (hspec ⟨r,hmem r hr⟩).1
  have had := hAd E C hblock hcenter hupper hbulk hspectator spectator hspec
    (spectatorList spectator ds) hmem l (hl) x y
    p q P Q c e hx hy hc he hs gs
  have hI := reference_plain_integrals_le C (hIntegral E C hblock hcenter)
    (bulkSize k₀ L/2) (spectatorList spectator ds)
    (fun r hr => (spectatorPrimes spectator ds r hr).pos) hout l
    x y p q P Q c e hx hy hc he hP hQ hPc hQc hs gs hmatch
    (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))) eB
  have := primeAtNeZero (spectatorPrimes spectator ds)
  have hlogs : ∀i : Fin (spectatorList spectator ds).length,
      Real.exp (L/2000) ≤ Real.log ((spectatorList spectator ds).get i:ℝ) := by
    intro i
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using
      (hspec ⟨(spectatorList spectator ds).get i,hmem _ (List.get_mem _ i)⟩).1
  have hflat' : ∀i : Fin (spectatorList spectator ds).length,
      (FiniteField.correlationBound (residueTransform d (primeAt (spectatorList spectator ds) i)):ℝ) ≤ ε := by
    intro i
    exact hflat ⟨primeAt (spectatorList spectator ds) i,hmem _ (List.get_mem _ i)⟩
  have hOp := hBudget l (hl) (spectatorList spectator ds) hlen _ _ hs gs
    (spectatorPrimes spectator ds) hV σ k₀ had hthree hgood hlogs hflat'
  exact ⟨hOp false _ (by simpa only [Fintype.card_prod,Fintype.card_fin] using hI.1),
    hOp true _ (by simpa only [Fintype.card_prod,Fintype.card_fin] using hI.2)⟩

end Ostmann.Arithmetic.HistoryBulkSelectedGoodOperator

end

end OAI
