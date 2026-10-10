import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementMain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistorySelectedPairDerivativeBounds PrimeCellFreezing
open HistoryBulkPriorGrid HistoryPrincipalIntegralAverage HistoryBulkReplacementGeometry
open HistoryBulkGiantIntegerReference HistoryBulkResidueNormSum ScaleBudget Filter

theorem spectatorPrimes (spectator : PrimeSource) {n : ℕ} (ds : Fin n→spectator.Sample) :
    ∀q∈spectatorList spectator ds,q.Prime := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact spectator.prime _ (ds i).property

theorem selected_corrected_prime_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k₀ : ℕ} (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
    (∀p : spectator.Sample, Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize k₀ L/2))→spectator.Sample,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
    1 < (C.giantCenter:ℝ) →
    ∀ (l : ℕ) (_hl : l < k₀)
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
    let outside := spectatorList spectator ds
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T (permutedAssignment C l σ x) q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    let eB := integerOrderedEquiv C V l outside σ x p q P Q c e hs
    ∀ (hV : ∀r∈outside,∀j≤l,V j<r) (independent : Bool),
    let N := bulkModulus h g outside k₀
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
    let F := rootTest independent false d h g hs gs (spectatorPrimes spectator ds) hV σ k₀
    let f := jointCorrectedScalar C (bulkSize k₀ L/2) h g hs gs (boolEquiv h g) eB
    ∃ hsize : (N:ℝ)<Real.exp (bulkLogLower L),
    ‖sourceBulkMean L E C.bulkPositive N hsize F (fun x=>primeIntegral
      (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>Construction.logCellMass C.giantCenter ∅)
      (fun y=>primeJointCutoff C.giantCenter f y x)) -
      HistorySelectedJointIntegralBounds.nestedPrimeIntegral L C.giantCenter E f*
        ResidueHaar.average F‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*PrimeCellFreezing.logCellMass
        (fun _ : Bool=>(Construction.logCellMass C.giantCenter ∅)⁻¹)
        (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) := by
  filter_upwards [prime_eventually Bs BD Bz (selectedExponent Bs BD Bz k₀) hk₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop 1] with L hAP hm
  have hm' : 1 ≤ bulkSize k₀ L := by exact_mod_cast hm
  intro spectator hspec ds E C hG l hl σ x p q P Q c e hx hc he hP hQ hPc hQc
  dsimp only
  intro hs gs hV independent
  let h := decodeHistory C.sources _ (frequencyBound Bs BD Bz k₀ L) l
    (giantState (sourceState C.sources _ x p) P Q) c
  let g := decodeHistory C.sources _ (frequencyBound Bs BD Bz k₀ L) l
    (giantState (sourceState C.sources _ (permutedAssignment C l σ x) q) P Q) e
  let : NeZero (bulkModulus h g (spectatorList spectator ds) k₀) :=
    ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
  obtain ⟨hsize,hrep⟩ := hAP spectator hspec ds l hl.le h g hs gs
  refine ⟨hsize,?_⟩
  have hout : (spectatorList spectator ds).length = 2*(bulkSize k₀ L/2) := by
    simp only [spectatorList,List.length_ofFn]
  have houtpos := fun r hr => (spectatorPrimes spectator ds r hr).pos
  have hf := selected_corrected_prime_joint_bounds C hBs hk₀ hm' (bulkSize k₀ L/2)
    (spectatorList spectator ds) houtpos hout l hl σ x p q P Q c e
    hx hc he hP hQ hPc hQc hs gs
  have hh := hrep d E C hG _
    (sum_norm_rootTest_le independent false d h g hs gs (spectatorPrimes spectator ds) hV σ k₀)
    _ hf.2 hf.1.continuous.continuousOn
  rw [prime_main_eq] at hh
  exact hh

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
