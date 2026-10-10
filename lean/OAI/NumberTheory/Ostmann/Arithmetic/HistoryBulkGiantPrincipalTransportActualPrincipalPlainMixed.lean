import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportActualPrincipalBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSelectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSelectedPlainMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion Filter ScaleBudget PrimeCellActualErrorBudget
open HistoryGiantWeightedPriorReplacement HistoryGiantReplacementError
open HistoryPrincipalIntegralAverage HistoryCRTIntegration ResidueHaar
open LogCellPartition HistoryGiantPriorGrid HistoryPairSmoothXi HistoryPairPattern
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryBulkGiantCorrectedBounds
open HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds HistoryGiantReferenceMean
open HistorySignedXiTransport HistorySymbolicEncoding
open HistoryBulkReferenceNewModuli HistoryPairBulkTransport

open HistorySignedSpectatorCRT HistoryBulkReferenceTests HistoryFrequencyResidues HistoryBulkResidueNormSum
open HistorySignedResidueFactorization HistorySignedResidueWeightedAverages
open HistoryDiagonalSmallAverage DiagonalSmallResidueNorm

theorem plain_mixed_actual_principal_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀p : spectator.Sample, Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ (ds : Fin (2*(bulkSize k₀ L/2))→spectator.Sample)
      (l : ℕ) (_hl : l ≤ k₀)
      (xn x₀ y₀ : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
      (snew s₀ t₀ P₀ Q₀ : ℤ) (gp gm : ℕ)
      (cnew c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
        (frequencyBound Bs BD Bz k₀ L) l)
      (_hxn : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass xn ≠ 0)
      (_hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x₀ ≠ 0)
      (_hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y₀ ≠ 0)
      (_hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
      (_he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
      (_hP : 0<P₀) (_hQ : 0<Q₀)
      (_hPc : |Real.log (P₀:ℝ)-(C.giantCenter:ℝ)|≤1)
      (_hQc : |Real.log (Q₀:ℝ)-(C.giantCenter:ℝ)|≤1),
    let outside := spectatorList spectator ds
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x₀ s₀) P₀ Q₀) c
    let k := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y₀ t₀) P₀ Q₀) e
    let newh := assignedHistory C.sources seed V l snew gp gm xn cnew
    ∀ (hs : h.Supported V outside) (ks : k.Supported V outside), RootMatching h k →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (eB : ι ≃ bulkCoordinates h k) (u : ι→ℝ),
      (∀i,0<u i) →
    ∀ (newk : History l) (m : ℕ) (σ : Equiv.Perm (Fin (2^l)×Fin m))
      (xUnits : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (k₀+2)))ˣ)
      (v : PairKey h k→ℤ)
      (outerU xs : List SmallSlot) (hslots : newh.root.small.Perm (outerU++xs))
      (D₀ P₁ q₁ : ℕ) (v₁ : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
      (huA : SmallUnitData D₀ P₁ q₁ outerU xs v₁)
      (_hcrt : NewCRTCompatible newh h k outside k₀),
    let M := newComparisonModulus newh h k outside k₀
    letI : NeZero M := ⟨(assigned_newComparisonModulus_pos C.sources seed V l snew gp gm
      xn cnew h k hs ks (selected_spectator_primes spectator ds) k₀).ne'⟩
    letI : NeZero (rootModulus newh) := neZero_of_dvd_modulus (new_A_dvd newh h k outside k₀)
    letI : NeZero outside.prod := neZero_of_dvd_modulus (new_D_dvd newh h k outside k₀)
    letI : NeZero (frequencyModulus h k (k₀+2)) := neZero_of_dvd_modulus (new_R_dvd newh h k outside k₀)
    letI : NeZero (representativeModulus h k) := neZero_of_dvd_modulus (new_B_dvd newh h k outside k₀)
    let fA := fun a => rootResidueIndicator newh a * mixedExtension
      (fun z => (rootSmallTest d newh outerU xs hslots D₀ P₁ q₁ v₁ huA z:ℂ)) a
    let R := newReferenceResidueTest d k₀ h k hs ks newh newk σ xUnits v fA
    ∀ (deleted : Finset ℕ), deleted.card≤2 → ∀hZ : 0<logCellMass C.giantCenter deleted,
    ‖guardedPeriodicSourceMixedMean C.giantCenter deleted hZ M R
        (fun v=>jointScalar C (bulkSize k₀ L/2) h k hs ks (optionEquiv h k) eB v u)-
      mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
        (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>logCellMass C.giantCenter deleted)
        (mixedGiantPrimeTest C.giantCenter (fun v=>jointScalar C (bulkSize k₀ L/2) h k hs ks (optionEquiv h k) eB v u))*
          (((∏i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value):ℝ):ℂ)*
            average (fun z : MixedPair outside.prod=>residuePairSpectator (residueTransform d)
              outside outside.prod newh newk (z.1,z.2))*
            average (fun z : MixedPair (frequencyModulus h k (k₀+2))=>independentRTest k₀ h k σ
              ((z.1:ZMod (frequencyModulus h k (k₀+2))),(z.2:ZMod (frequencyModulus h k (k₀+2)))) xUnits)*
            average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)))‖≤
      9*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [plain_mixed_selected_eventually d Bs BD Bz hBs hk₀] with L hselected
  intro E C hG hGu hcl hcu hb hd spectator hspec ds l hl xn x₀ y₀ snew s₀ t₀ P₀ Q₀ gp gm
    cnew c e hxn hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs ks hmatch ι _ _ eB u hu newk m σ xUnits v outerU xs hslots D₀ P₁ q₁ v₁ _ huA hcrt
    deleted hdeleted hZ
  let h := decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x₀ s₀) P₀ Q₀) c
  let k := decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y₀ t₀) P₀ Q₀) e
  let newh := assignedHistory C.sources _ _ l snew gp gm xn cnew
  let outside := spectatorList spectator ds
  let M := newComparisonModulus newh h k outside k₀
  let : NeZero M := ⟨(assigned_newComparisonModulus_pos C.sources _ _ l snew gp gm
    xn cnew h k hs ks (selected_spectator_primes spectator ds) k₀).ne'⟩
  let : NeZero (rootModulus newh) := neZero_of_dvd_modulus (new_A_dvd newh h k outside k₀)
  let : NeZero outside.prod := neZero_of_dvd_modulus (new_D_dvd newh h k outside k₀)
  let : NeZero (frequencyModulus h k (k₀+2)) := neZero_of_dvd_modulus (new_R_dvd newh h k outside k₀)
  let : NeZero (representativeModulus h k) := neZero_of_dvd_modulus (new_B_dvd newh h k outside k₀)
  have hbound := hselected E C hG hGu hcl hcu hb hd spectator hspec ds l hl xn x₀ y₀
    snew s₀ t₀ P₀ Q₀ gp gm cnew c e hxn hx hy hc he hP hQ hPc hQc hs ks hmatch
    ι eB u hu newk m σ xUnits v
    (fun a => rootResidueIndicator newh a * mixedExtension
      (fun z => (rootSmallTest d newh outerU xs hslots D₀ P₁ q₁ v₁ huA z:ℂ)) a)
    (norm_mixed_rootSmallTest_le d newh outerU xs hslots D₀ P₁ q₁ v₁ huA)
    deleted hdeleted hZ
  have havg := new_reference_mixed_small_average_of_modulus k₀ h k hs ks newh newk d σ xUnits v
    hcrt outerU xs hslots D₀ P₁ q₁ v₁ huA
  rw [havg] at hbound
  exact hbound

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
