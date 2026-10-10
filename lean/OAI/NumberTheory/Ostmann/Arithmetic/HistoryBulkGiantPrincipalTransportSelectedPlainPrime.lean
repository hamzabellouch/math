import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportIntegerSourcePlainPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSelectedBasic
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

theorem plain_prime_selected_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      (l : ℕ) (_ : l ≤ k₀)
      (xn x₀ y₀ : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
      (snew s₀ t₀ P₀ Q₀ : ℤ) (gp gm : ℕ)
      (cnew c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
        (frequencyBound Bs BD Bz k₀ L) l)
      (_ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass xn ≠ 0)
      (_ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x₀ ≠ 0)
      (_ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y₀ ≠ 0)
      (_ : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
      (_ : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
      (_ : 0<P₀) (_ : 0<Q₀)
      (_ : |Real.log (P₀:ℝ)-(C.giantCenter:ℝ)|≤1)
      (_ : |Real.log (Q₀:ℝ)-(C.giantCenter:ℝ)|≤1),
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
      (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ),
      (∀z,‖fA z‖≤(rootModulus newh:ℝ)) →
    let M := newComparisonModulus newh h k outside k₀
    letI : NeZero M := ⟨(assigned_newComparisonModulus_pos C.sources seed V l snew gp gm
      xn cnew h k hs ks (selected_spectator_primes spectator ds) k₀).ne'⟩
    let R := newReferenceResidueTest d k₀ h k hs ks newh newk σ xUnits v fA
    ∀ (deleted : Finset ℕ), deleted.card≤2 → ∀hZ : 0<logCellMass C.giantCenter deleted,
    ‖guardedPeriodicSourcePrimeMean C.giantCenter deleted hZ M R
        (fun v=>jointScalar C (bulkSize k₀ L/2) h k hs ks (boolEquiv h k) eB v u)-
      primeIntegral (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>logCellMass C.giantCenter deleted)
        (primeCutoff C.giantCenter (fun v=>jointScalar C (bulkSize k₀ L/2) h k hs ks (boolEquiv h k) eB v u))*
          average (fun z : UnitPair M=>R (z.1,z.2))‖≤
      30*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [plain_prime_integer_source_eventually d Bs BD Bz hBs hk₀,
    selected_newComparisonModulus_cap_eventually d Bs BD Bz hk₀] with L hsource hcap
  intro E C hG hGu hcl hcu hb hd spectator hspec ds l hl xn x₀ y₀ snew s₀ t₀ P₀ Q₀ gp gm
    cnew c e hxn hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs ks hmatch ι _ _ eB u hu newk m σ xUnits v fA hWA deleted hdeleted hZ
  have hout := selected_spectator_primes spectator ds
  have hsize := hcap E C hG hcl hcu hb hd spectator hspec ds l hl
    xn x₀ y₀ snew s₀ t₀ gp gm P₀ Q₀ cnew c e hxn hx hy hc he hs ks
  let M := newComparisonModulus
    (assignedHistory C.sources _ _ l snew gp gm xn cnew)
    (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x₀ s₀) P₀ Q₀) c)
    (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y₀ t₀) P₀ Q₀) e)
    (spectatorList spectator ds) k₀
  let : NeZero M := ⟨hsize.1.ne'⟩
  have hmod : Real.log (M:ℝ)≤Real.exp (giant.μ*L) := by
    simpa only [giant, show (12/1000:ℝ)=(3/250:ℝ) by norm_num] using hsize.2.1
  have hbudget := new_reference_test_budget d k₀ _ _ hs ks
    (assignedHistory C.sources _ _ l snew gp gm xn cnew) newk σ xUnits v fA hout hWA
  have ha : 3+2^(l+1)≤residueCostExponent k₀ := by
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ))
      (Nat.add_le_add_right hl 1)) 3
  exact hsource E C hG hGu hcl hcu hb hd l (bulkSize k₀ L/2)
    (spectatorList spectator ds) (fun q hq=>(hout q hq).pos)
    (by simp [spectatorList]) hl x₀ y₀ s₀ t₀ P₀ Q₀ c e hx hy hc he hP hQ hPc hQc
    hs ks hmatch ι eB u hu M hmod deleted hdeleted hZ (3+2^(l+1)) ha _
    hbudget.1 hbudget.2.1

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
