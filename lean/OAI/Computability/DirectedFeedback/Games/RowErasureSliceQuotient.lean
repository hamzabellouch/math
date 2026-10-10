import Mathlib
import OAI.Computability.DirectedFeedback.Analysis.PrivateFourier
import OAI.Computability.DirectedFeedback.Analysis.NoiseEnumeration

namespace OAI

namespace DFVSGames.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

theorem exists_direction_of_row_and_column (A : K →ₗ[R] L)
    (Q : Submodule R E) (B : E →ₗ[R] K)
    (hQ : Q ≤ B.ker) (hA : LinearMap.range B ≤ A.ker) :
    ∃ N : (E ⧸ Q) →ₗ[R] A.ker, direction A Q N = B := by
  let B' : E →ₗ[R] A.ker := B.codRestrict A.ker
    (fun x => hA ⟨x, rfl⟩)
  have hQ' : Q ≤ B'.ker := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change B q = 0
    exact hQ hq
  refine ⟨Q.liftQ B' hQ', ?_⟩
  ext x
  rfl

theorem direction_injective (A : K →ₗ[R] L) (Q : Submodule R E) :
    Function.Injective (direction A Q) := by
  intro N P h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : E →ₗ[R] K => f v) h

def AffineSlice (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :=
  {M : E →ₗ[R] K // A.comp M = A.comp M₀ ∧ ∀ q ∈ Q, M q = M₀ q}

def ofQuotient (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : AffineSlice A Q M₀ := by
  refine ⟨M₀ + direction A Q N, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change A (M₀ x + (N (Q.mkQ x) : K)) = A (M₀ x)
    rw [map_add, show A (N (Q.mkQ x) : K) = 0 from (N (Q.mkQ x)).property,
      add_zero]
  · intro q hq
    have hz : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hq
    simp [direction, hz]

@[simp] theorem ofQuotient_val (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    (ofQuotient A Q M₀ N).val = M₀ + direction A Q N := rfl

theorem ofQuotient_bijective (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) : Function.Bijective (ofQuotient A Q M₀) := by
  constructor
  · intro N P h
    apply direction_injective A Q
    exact add_left_cancel (congrArg Subtype.val h)
  · intro M
    have hQ : Q ≤ (M.val - M₀).ker := by
      intro q hq
      change M.val q - M₀ q = 0
      exact sub_eq_zero.mpr (M.property.2 q hq)
    have hA : LinearMap.range (M.val - M₀) ≤ A.ker := by
      rintro y ⟨x, rfl⟩
      change A (M.val x - M₀ x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrArg (fun f : E →ₗ[R] L => f x) M.property.1
    obtain ⟨N, hN⟩ := exists_direction_of_row_and_column A Q (M.val - M₀) hQ hA
    refine ⟨N, ?_⟩
    apply Subtype.ext
    rw [ofQuotient_val, hN]
    simpa only [← add_sub_assoc] using add_sub_cancel_left M₀ M.val

def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

theorem equiv_affine_target (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) (z : E) (u : K) :
    (equiv A Q M₀ N).val z + u =
      (N (Q.mkQ z) : K) + (M₀ z + u) := by
  change (M₀ z + (N (Q.mkQ z) : K)) + u = _
  ac_rfl

theorem expect_equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    [Fintype ((E ⧸ Q) →ₗ[R] A.ker)] [Fintype (AffineSlice A Q M₀)]
    (f : AffineSlice A Q M₀ → ℝ) :
    Finset.univ.expect (fun N => f (equiv A Q M₀ N)) = Finset.univ.expect f := by
  exact Fintype.expect_equiv (equiv A Q M₀) _ _ (fun _ => rfl)

end
end DFVSGames.Inverse.RowErasureSliceQuotient

noncomputable section

namespace DFVSGames.Decoder.TransferredDecoding

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open DFVSGames.Inverse

attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

def privateOrigin (A : K →ₗ[F2] R) (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val) : E →ₗ[F2] A.ker :=
  AdviceFibers.kernelDifference A rows.val (AdviceFibers.observedBase A rows)
    (AdviceFibers.observedBase_property A rows) ⟨Mstar, hstar⟩

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

def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

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

end DFVSGames.Decoder.TransferredDecoding
end

noncomputable section

namespace DFVSGames.Decoder.VisiblePolicies

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

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

def pointLaw {X : Type*} [Fintype X] (x : X) : FiniteDistribution X where
  weight y := if y = x then 1 else 0
  nonnegative y := by split <;> norm_num
  normalized := by simp

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

def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

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

end DFVSGames.Decoder.VisiblePolicies
end

namespace DFVSGames.Clean.IncidenceGap

open DFVSGames.Foundations.Games
open DFVSGames.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

local instance accepts_decidable (g : Incidence O N) (o : O) (i : Fin 3)
    (a : Triple) (b : Bool) : Decidable (g.accepts o i a b) :=
  inferInstanceAs (Decidable (xorTriple a = g.rhs o ∧ a i = b))

def slotLaw (ω : FiniteDistribution O) : FiniteDistribution (O × Fin 3) :=
  ω.product (FiniteDistribution.uniform (Fin 3))

@[simp] theorem slotLaw_weight (ω : FiniteDistribution O) (o : O) (i : Fin 3) :
    (slotLaw ω).weight (o, i) = ω.weight o / 3 := by
  simp [slotLaw, FiniteDistribution.product, FiniteDistribution.uniform, div_eq_mul_inv]

def incidenceLaw (g : Incidence O N) (ω : FiniteDistribution O) :
    FiniteDistribution (O × N) :=
  (slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))

def game (g : Incidence O N) (ω : FiniteDistribution O) : Game O N Triple Bool := by
  classical
  exact { questions := incidenceLaw g ω
          accepts := fun o n a b => decide (g.namedAccepts o n a b) }

@[simp] theorem game_accepts_iff (g : Incidence O N) (ω : FiniteDistribution O)
    (o : O) (n : N) (a : Triple) (b : Bool) :
    (game g ω).accepts o n a b = true ↔ g.namedAccepts o n a b := by
  classical
  simp [game]

theorem game_isProjection (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    DFVSGames.Repetition.IsProjection (game g ω) := by
  intro o n a b b' hb hb'
  obtain ⟨i, hi, _, hai⟩ := (game_accepts_iff g ω o n a b).mp hb
  obtain ⟨j, hj, _, haj⟩ := (game_accepts_iff g ω o n a b').mp hb'
  have hij := distinct o i j (hi.trans hj.symm)
  subst j
  exact hai.symm.trans haj

def paritySuccess (g : Incidence O N) (ω : FiniteDistribution O) (b : N → Bool) : ℝ :=
  ω.probability (fun o => decide (xorTriple (fun i => b (g.name o i)) = g.rhs o))

def parityValue (g : Incidence O N) (ω : FiniteDistribution O) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (paritySuccess g ω)

theorem paritySuccess_le_parityValue (g : Incidence O N) (ω : FiniteDistribution O)
    (b : N → Bool) : paritySuccess g ω b ≤ parityValue g ω := by
  classical
  exact Finset.le_sup' (paritySuccess g ω) (Finset.mem_univ b)

theorem local_count_bound (a b : Triple) (rhs : Bool) :
    (∑ i : Fin 3, if xorTriple a = rhs ∧ a i = b i then (1 : ℝ) else 0) ≤
      2 + if xorTriple b = rhs then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_three]
  by_cases ha : xorTriple a = rhs
  · by_cases hb : xorTriple b = rhs
    · simp only [ha, hb, true_and, ite_true]
      split_ifs <;> norm_num
    · by_cases h0 : a 0 = b 0 <;> by_cases h1 : a 1 = b 1 <;>
        by_cases h2 : a 2 = b 2 <;> simp_all [xorTriple] <;> norm_num
  · simp only [ha, false_and, ite_false, zero_add]
    split_ifs <;> norm_num

theorem game_success_eq_slot_average (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) =
      ∑ o, ω.weight o * ((∑ i : Fin 3,
        if g.accepts o i (a o) (b (g.name o i)) then (1 : ℝ) else 0) / 3) := by
  classical
  unfold Game.success
  change ((slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Game.wins, game, decide_eq_true_eq, slotLaw_weight,
    Incidence.namedAccepts_iff_accepts g distinct]
  by_cases h : g.accepts o i (a o) (b (g.name o i)) <;> simp [h, div_eq_mul_inv]

theorem game_success_honest_eq_paritySuccess
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (b : N → Bool) :
    (game g ω).success ((fun o i => b (g.name o i)), b) = paritySuccess g ω b := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  unfold paritySuccess FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : xorTriple (fun i => b (g.name o i)) = g.rhs o <;>
    simp [Incidence.accepts, h]

theorem parityValue_le_game_value
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    parityValue g ω ≤ (game g ω).value := by
  classical
  unfold parityValue
  apply Finset.sup'_le
  intro b _
  rw [← game_success_honest_eq_paritySuccess g ω distinct b]
  exact Game.success_le_value _ _

theorem game_success_le_two_add_parity_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) ≤ (2 + paritySuccess g ω b) / 3 := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  calc
    _ ≤ ∑ o, ω.weight o * ((2 + if xorTriple (fun i => b (g.name o i)) =
        g.rhs o then (1 : ℝ) else 0) / 3) := by
      apply Finset.sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_left _ (ω.nonnegative o)
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact local_count_bound (a o) (fun i => b (g.name o i)) (g.rhs o)
    _ = (2 + paritySuccess g ω b) / 3 := by
      simp_rw [← mul_div_assoc, mul_add]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ω.normalized]
      simp only [one_mul, paritySuccess, FiniteDistribution.probability,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem game_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (game g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  have hv := paritySuccess_le_parityValue g ω s.2
  linarith

theorem game_value_le_one_sub_gap_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (gap : ℝ) (hgap : ∀ b : N → Bool, paritySuccess g ω b ≤ 1 - gap) :
    (game g ω).value ≤ 1 - gap / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  linarith [hgap s.2]

theorem game_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (game g ω).value ≤ (14 : ℝ) / 15 := by
  have h := game_value_le_one_sub_third g ω distinct
  linarith

def satisfyingTriple (rhs : Bool) (a : Bool × Bool) : Triple :=
  fun i => if i = 0 then a.1 else if i = 1 then a.2 else (a.1 ^^ a.2) ^^ rhs

theorem satisfyingTriple_valid (rhs : Bool) (a : Bool × Bool) :
    xorTriple (satisfyingTriple rhs a) = rhs := by
  have h : ∀ x y z : Bool, ((x ^^ y) ^^ ((x ^^ y) ^^ z)) = z := by decide
  exact h a.1 a.2 rhs

theorem satisfyingTriple_of_valid (a : Triple) (rhs : Bool)
    (valid : xorTriple a = rhs) : satisfyingTriple rhs (a 0, a 1) = a := by
  have h : ∀ x y z : Bool, ((x ^^ y) ^^ ((x ^^ y) ^^ z)) = z := by decide
  funext i
  fin_cases i
  · rfl
  · rfl
  · change ((a 0 ^^ a 1) ^^ rhs) = a 2
    rw [← valid]
    exact h (a 0) (a 1) (a 2)

def fourAnswerGame (g : Incidence O N) (ω : FiniteDistribution O) :
    Game O N (Bool × Bool) Bool where
  questions := incidenceLaw g ω
  accepts o n a b := (game g ω).accepts o n (satisfyingTriple (g.rhs o) a) b

theorem four_answer_card : Fintype.card (Bool × Bool) = 4 := by decide

theorem fourAnswerGame_isProjection
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    DFVSGames.Repetition.IsProjection (fourAnswerGame g ω) := by
  intro o n a b b' hb hb'
  exact game_isProjection g ω distinct o n (satisfyingTriple (g.rhs o) a) b b' hb hb'

theorem fourAnswerGame_accepts_encode
    (g : Incidence O N) (ω : FiniteDistribution O)
    (o : O) (n : N) (a : Triple) (b : Bool)
    (h : (game g ω).accepts o n a b = true) :
    (fourAnswerGame g ω).accepts o n (a 0, a 1) b = true := by
  have valid : xorTriple a = g.rhs o := by
    obtain ⟨_, _, hv, _⟩ := (game_accepts_iff g ω o n a b).mp h
    exact hv
  change (game g ω).accepts o n (satisfyingTriple (g.rhs o) (a 0, a 1)) b = true
  rw [satisfyingTriple_of_valid a (g.rhs o) valid]
  exact h

theorem fourAnswerGame_value_eq (g : Incidence O N) (ω : FiniteDistribution O) :
    (fourAnswerGame g ω).value = (game g ω).value := by
  apply le_antisymm
  · apply (Game.value_le_iff _ _).mpr
    intro s
    change (game g ω).success
      ((fun o => satisfyingTriple (g.rhs o) (s.1 o)), s.2) ≤ (game g ω).value
    exact Game.success_le_value _ _
  · apply (Game.value_le_iff _ _).mpr
    intro s
    calc
      (game g ω).success s ≤
          (fourAnswerGame g ω).success ((fun o => (s.1 o 0, s.1 o 1)), s.2) := by
        apply FiniteDistribution.probability_mono
        intro q h
        exact fourAnswerGame_accepts_encode g ω q.1 q.2 (s.1 q.1) (s.2 q.2) h
      _ ≤ (fourAnswerGame g ω).value := Game.success_le_value _ _

theorem fourAnswerGame_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (fourAnswerGame g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  rw [fourAnswerGame_value_eq]
  exact game_value_le_one_sub_third g ω distinct

theorem fourAnswerGame_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (fourAnswerGame g ω).value ≤ (14 : ℝ) / 15 := by
  rw [fourAnswerGame_value_eq]
  exact game_value_le_fourteen_fifteenths g ω distinct hopt

end
end DFVSGames.Clean.IncidenceGap

namespace DFVSGames.Clean.Bound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Experiment

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [DecidableEq N] in

theorem repeated_incidence_value_le
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) (n : ℕ) :
    ((incidenceGame g ((IncidenceGap.slotLaw ω).pushforward (incidence g.name))).repetition n).value ≤
      (1 - (1 : ℝ) / 3600) ^ n := by
  change ((IncidenceGap.game g ω).repetition n).value ≤ _
  exact Repetition.clean_repetition_value (IncidenceGap.game g ω)
    (IncidenceGap.game_isProjection g ω distinct) n
    (IncidenceGap.game_value_le_fourteen_fifteenths g ω distinct hopt)

theorem clean_success_le (k : ℕ) (g : IncidenceExtraction.Incidence O N)
    (ω : FiniteDistribution O) (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    success k (IncidenceGap.slotLaw ω) g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) / 3600) ^ k := by
  have h := success_le_of_repetition k (IncidenceGap.slotLaw ω) g extraLaw
    β hβ₀ hβ₁ strategy distinct (1 - (1 : ℝ) / 3600)
    (repeated_incidence_value_le g ω distinct hopt)
  convert h using 1 ; congr 1 ; ring

theorem clean_success_le_dimension (k : ℕ) (g : IncidenceExtraction.Incidence O N)
    (ω : FiniteDistribution O) (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    success k (IncidenceGap.slotLaw ω) g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have comparison := clean_mask_moment_le_dimension β hβ₀ hβ₁
    (ZeroInformation.zero : Coefficient R) k dimW rs hcard
  rw [clean_mask_moment] at comparison
  have estimate := success_le_of_repetition k (IncidenceGap.slotLaw ω) g extraLaw
    β hβ₀ hβ₁ strategy distinct (1 - (1 : ℝ) / 3600)
    (repeated_incidence_value_le g ω distinct hopt)
  exact estimate.trans comparison

theorem native_clean_success_le_dimension (k : ℕ)
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : NativeExperiment.MaskStrategy k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    NativeExperiment.success k (IncidenceGap.slotLaw ω) g β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  rw [NativeExperiment.success_eq_flat]
  exact clean_success_le_dimension k g ω (FiniteDistribution.uniform (Additional k R))
    β hβ₀ hβ₁ (NativeExperiment.liftStrategy strategy) distinct hopt dimW rs hcard

end
end DFVSGames.Clean.Bound

namespace DFVSGames.Clean.ActualAdviceBound

open Foundations.Games Integration.BinaryLinear
open Soundness
open AnswerBridge

noncomputable section

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D] [Fintype D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

theorem deterministic_success_le_dimension (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have hcard' : Fintype.card (Experiment.Coefficient Q) ≤ 2 ^ (dimW + rs) :=
    (Fintype.card_congr (bitsCoordinatesEquiv coordinates).symm).le.trans hcard
  exact (ActualAdviceBridge.success_le_native coordinates (IncidenceGap.slotLaw ω)
    g policy β hβ₀ hβ₁).trans (Bound.native_clean_success_le_dimension k g ω β hβ₀ hβ₁
      (ActualAdviceBridge.nativeStrategy coordinates g policy) distinct hopt dimW rs hcard')

theorem stochastic_success_le_dimension (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have hcard' : Fintype.card (Experiment.Coefficient Q) ≤ 2 ^ (dimW + rs) :=
    (Fintype.card_congr (bitsCoordinatesEquiv coordinates).symm).le.trans hcard
  obtain ⟨strategy, h⟩ := ActualAdviceStochasticBridge.success_le_some_native coordinates
    (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁
  exact h.trans (Bound.native_clean_success_le_dimension k g ω β hβ₀ hβ₁
    strategy distinct hopt dimW rs hcard')

theorem stochastic_success_le_dimension_finite [FiniteDimensional F2 D]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k :=
  stochastic_success_le_dimension finiteCoordinates g ω policy β hβ₀ hβ₁
    distinct hopt dimW rs hcard

end
end DFVSGames.Clean.ActualAdviceBound

end OAI
