import Mathlib
import OAI.Computability.MaxCut.Encoding.PrivateFourier
import OAI.Computability.MaxCut.Encoding.TableKeysGame
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient

namespace OAI

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace MaxCutGames.Decoder.TransferredDecoding

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open MaxCutGames.Inverse

attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- Equality indicators depend on their propositions, not on the chosen
computable or classical decision procedures. Both deciders are explicit. -/
theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

/-- The slice origin, expressed relative to the fixed visible row base. -/
def privateOrigin (A : K →ₗ[F2] R) (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val) : E →ₗ[F2] A.ker :=
  AdviceFibers.kernelDifference A rows.val (AdviceFibers.observedBase A rows)
    (AdviceFibers.observedBase_property A rows) ⟨Mstar, hstar⟩

/-- Rebase the complete quotient parametrization without changing its matrices. -/
theorem assemble_privateOrigin (A : K →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val)
    (Q : Submodule F2 E) (L : (E ⧸ Q) →ₗ[F2] A.ker) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        (RowErasureSliceQuotient.equiv A Q Mstar L).val := by
  ext x
  change AdviceFibers.observedBase A rows x +
      ((Mstar x - AdviceFibers.observedBase A rows x) + (L (Q.mkQ x) : K)) =
    Mstar x + (L (Q.mkQ x) : K)
  rw [← add_assoc]
  congr 1
  rw [add_comm, sub_add_cancel]

end Rebase

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

/-- A default actual projected answer depends only on the displayed positions. -/
def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

/-- Exact transport from the actual conditional matrix slice to the private
Fourier coordinates.  `targetIntercept` uses the visible base, not `Mstar`. -/
theorem actual_slice_agreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val) (Q : Submodule F2 (RawPartnerTarget.RawPoint J))
    [Fintype ((RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar)]
    (z' : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    (𝔼 M : RowErasureSliceQuotient.AffineSlice A Q Mstar,
      if TableKeysRestoration.projectedAnswer S k s d labeling J O (M.val.prod T) =
        M.val z' + u then (1 : ℝ) else 0) =
    𝔼 L : (RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker,
      if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
          (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        TableKeysPrivateRow.targetIntercept J A rows z' u +
          ((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' : Alphabet s)
      then (1 : ℝ) else 0 := by
  rw [← RowErasureSliceQuotient.expect_equiv A Q Mstar]
  apply Finset.expect_congr rfl
  intro L _
  rw [← assemble_privateOrigin A rows Mstar hstar Q L]
  change (if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' + u
    then (1 : ℝ) else 0) = _
  rw [TableKeysPrivateRow.affine_target_on_row J A rows
    (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' u]
  rw [add_comm (((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z') : Alphabet s)
    (TableKeysPrivateRow.targetIntercept J A rows z' u)]

/-- Private policies for an actual restored labeling satisfy the conditional
decoding bound on every transferred good slice.  Folding and first-bit
preservation come from their concrete constructions, not additional premises. -/
theorem actual_transferred_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val)
    (Z : Submodule F2 (ActualHomogeneous.E k)) [Fintype Z]
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1)
    (u : Alphabet s) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 A.ker ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    [Fintype A.ker]
    [Fintype (RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)]
    [Fintype (A.ker →ₗ[F2] RawPartnerTarget.RawPoint J)]
    [Fintype (A.ker →ₗ[F2] Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))]
    [Fintype ((RawPartnerTarget.RawPoint J ⧸
      Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A
      (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar)]
    (hsmall : 1 / (Fintype.card A.ker : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤
      𝔼 M : RowErasureSliceQuotient.AffineSlice A
          (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar,
        if TableKeysRestoration.projectedAnswer S k s d labeling J
            (RawPrivateTable.supported J (ActualGame.names S) occ slot) (M.val.prod T) =
          M.val (RawPrivateTable.projection J (ActualGame.rhs S) occ slot z) + u
        then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      PrivateStrategy.conditionalAgreement Z z ActualHomogeneous.tau hz
        (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)
        (TableKeysPrivateRow.rowAnswer S labeling J
          (RawPrivateTable.supported J (ActualGame.names S) occ slot) A rows T)
        A.ker.subtype (TableKeys.visibleTau J) (visibleFallback J) := by
  let π := RawPrivateTable.projection J (ActualGame.rhs S) occ slot
  let O := RawPrivateTable.supported J (ActualGame.names S) occ slot
  have hτ : (TableKeys.visibleTau J).comp π = ActualHomogeneous.tau := by
    apply LinearMap.ext
    intro x
    exact TableKeys.projection_preserves_homogeneous J (ActualGame.rhs S) occ slot x
  apply conditionalAgreement_from_slice Z z ActualHomogeneous.tau hz π
    (privateOrigin A rows Mstar hstar)
    (TableKeysPrivateRow.rowAnswer S labeling J O A rows T)
    A.ker.subtype Subtype.val_injective (TableKeys.visibleTau J) (visibleFallback J) hτ
    (TableKeysPrivateRow.rowAnswer_fold S labeling J O A rows T)
    (TableKeysPrivateRow.targetIntercept J A rows (π z) u)
    α hα ℓ r hH hZ hsmall
  apply hagreement.trans_eq
  calc
    _ = _ := actual_slice_agreement_eq_private S labeling J O A rows T Mstar hstar
      (Z.map π) (π z) u
    _ = _ := by
      apply Finset.expect_congr rfl
      intro L _
      exact indicator_congr _ _ _ _ Iff.rfl

end MaxCutGames.Decoder.TransferredDecoding

namespace MaxCutGames.Decoder.VisiblePolicies

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The part of a normalized affine witness needed by the left sampler. -/
structure ResponseWitness (k : ℕ) where
  columns : Submodule F2 (ActualHomogeneous.E k)
  coefficient : ActualHomogeneous.E k
  firstBit : ActualHomogeneous.tau coefficient = 1

def defaultWitness (k : ℕ) : ResponseWitness k :=
  ⟨⊥, ActualHomogeneous.hBasis k, ActualHomogeneous.tau_hBasis⟩

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

abbrev LeftInput (S : Source) (k s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.FullAdvice k (Fin S.occurrences) (Alphabet s) (Vector d) R

abbrev RightInput (S : Source) (J : Finset (Fin k)) (s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.ProjectedAdvice (K := Alphabet s) (W := Vector d) (R := R)
    (ActualGame.names S) J

/-- The witness choice has only the left observation as its variable input. -/
def chosenWitness {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : ResponseWitness k :=
  if h : ∃ w, good q w then Classical.choose h else defaultWitness k

theorem chosenWitness_spec {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) (h : ∃ w, good q w) :
    good q (chosenWitness good q) := by
  rw [chosenWitness, dite_eq_left h]
  exact Classical.choose_spec h

def leftPolicy {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : FiniteDistribution (ActualAnswer (ActualHomogeneous.tau (k := k))) :=
  let w := chosenWitness good q
  candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit

/-- A fixed valid fallback gives a total policy even on impossible row inputs. -/
def pointLaw {X : Type*} [Fintype X] (x : X) : FiniteDistribution X where
  weight y := if y = x then 1 else 0
  nonnegative y := by split <;> norm_num
  normalized := by simp

/-- The right kernel consumes its own complete visible observation only. -/
def rightPolicy (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R) :
    FiniteDistribution (ActualAnswer (TableKeys.visibleTau J)) :=
  if h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows then
    privateLaw
      (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
      q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J)
  else pointLaw (TransferredDecoding.visibleFallback J)

theorem rightPolicy_on_attainable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R)
    (h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows) :
    rightPolicy S labeling J q =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
        q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J) := by
  rw [rightPolicy, dite_eq_left h]

theorem leftPolicy_changeHidden (S : Source)
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R)
    (N : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] draw.rowMap.ker) :
    leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S)
      (AdviceExperiment.changeHidden draw N)) =
      leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) := by
  rw [AdviceExperiment.leftObservation_changeHidden]

theorem rightPolicy_on_draw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2 =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [rightPolicy_on_attainable S labeling draw.singletons
    (AdviceExperiment.rightObservation (ActualGame.names S) draw).2
    (AdviceExperiment.right_rows_attainable (ActualGame.names S) draw)]
  rfl

/-- The literal product of the two observation-local stochastic responses. -/
def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

/-- The private-decoding expression is exactly the actual local-kernel product
probability.  In particular there is no shared decoder random tape. -/
theorem observedAgreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    observedAgreement S labeling good draw =
      let w := chosenWitness good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
      PrivateStrategy.conditionalAgreement w.columns w.coefficient
        ActualHomogeneous.tau w.firstBit (AdviceExperiment.projection (ActualGame.rhs S) draw)
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [observedAgreement, rightPolicy_on_draw S labeling draw]
  dsimp only [PrivateStrategy.conditionalAgreement, leftPolicy]
  congr 1
  funext answers
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

end MaxCutGames.Decoder.VisiblePolicies
end

end OAI
