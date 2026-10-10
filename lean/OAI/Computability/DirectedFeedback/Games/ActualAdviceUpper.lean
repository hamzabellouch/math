import Mathlib
import OAI.Computability.DirectedFeedback.Games.AdviceLaw
import OAI.Computability.DirectedFeedback.Games.RowErasureSliceQuotient

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.ActualAdviceUpper

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.«variables») where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

def actualDraw (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs) where
  singletons := J
  occurrences := occ
  positions := slot
  rowMap := A
  hiddenMatrix := M
  complement := T

theorem fullInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    fullInput S A occ ((AdviceLaw.visibleMap A T M).comp
      (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) =
      AdviceExperiment.leftObservation (ActualGame.rhs S) (actualDraw S A J occ slot T M) :=
  rfl

theorem projectedInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    projectedInput S A J (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M) =
      (AdviceExperiment.rightObservation (ActualGame.names S)
        (actualDraw S A J occ slot T M)).2 :=
  rfl

theorem policyAgreement_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (occ : Fin k → Fin S.occurrences) (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    (((policies S labeling good A).first J occ
        ((AdviceLaw.visibleMap A T M).comp
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))).product
      ((policies S labeling good A).second J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M))).probability
        (fun answers => decide
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot answers.1.val =
            answers.2.val)) =
      VisiblePolicies.observedAgreement S labeling good (actualDraw S A J occ slot T M) := by
  dsimp only [policies, sourceIncidence]
  rw [fullInput_actual S A J occ slot T M, projectedInput_actual S A J occ slot T M]
  rfl

theorem source_projection_eq (S : Source) (J : Finset (Fin k))
    (draw : Fin k → Fin S.occurrences × Fin 3) :
    Clean.ActualAdviceBridge.projection (sourceIncidence S) J draw =
      RawPrivateTable.projection J (ActualGame.rhs S) (fun j => (draw j).1)
        (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) := by
  simp only [Clean.ActualAdviceBridge.projection, sourceIncidence,
    RawPrivateTable.projection, ActualGame.rhs, toBit_ofBit]

theorem fixed_public_map_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [AdviceLaw.actualSuccess_eq_cleanSuccess]
  exact Clean.ActualAdviceBound.stochastic_success_le_dimension_finite g ω policy
    β hβ₀ hβ₁ distinct hopt d rs (Clean.AdviceImageLaw.visible_card_binary_le d rs A)

theorem public_map_average_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : (A : Alphabet s →ₗ[F2] Vector rs) →
      Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A
          (policy A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  calc
    _ ≤ (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun _ => (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k) :=
      Clean.ActualAdviceBridge.expectation_mono _
        (fun A => fixed_public_map_bound g ω A (policy A) β hβ₀ hβ₁ distinct hopt)
    _ = _ := by
      rw [FiniteDistribution.expectation, ← Finset.sum_mul,
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).normalized, one_mul]

theorem actual_source_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          (sourceIncidence S) A (policies S labeling good A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k :=
  public_map_average_bound (sourceIncidence S) (FiniteDistribution.uniform (Fin S.occurrences))
    (policies S labeling good) β hβ₀ hβ₁ distinct hopt

end

end DFVSGames.Decoder.ActualAdviceUpper
end

section

namespace DFVSGames.Reduction.ActualCompleteness

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

section Evaluation
variable {E R : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup R] [Module F2 R] [Fintype R] [Fintype (E →ₗ[F2] R)]

theorem expect_linear_eval (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1)
    (g : R → ℚ) :
    (𝔼 X : E →ₗ[F2] R, g (X x)) = 𝔼 r : R, g r := by
  classical
  have hinv (r : R) : (𝔼 X : E →ₗ[F2] R, g (X x + r)) =
      𝔼 X : E →ₗ[F2] R, g (X x) := by
    let e : (E →ₗ[F2] R) ≃ (E →ₗ[F2] R) := Equiv.addRight (τ.smulRight r)
    apply Fintype.expect_equiv e
    intro X
    simp [e, hx]
  calc
    (𝔼 X : E →ₗ[F2] R, g (X x)) =
        𝔼 r : R, 𝔼 X : E →ₗ[F2] R, g (X x + r) := by simp only [hinv, Fintype.expect_const]
    _ = 𝔼 X : E →ₗ[F2] R, 𝔼 r : R, g (X x + r) := Finset.expect_comm _ _ _
    _ = 𝔼 r : R, g r := by
      have hshift (a : R) : (𝔼 r : R, g (a + r)) = 𝔼 r : R, g r := by
        apply Fintype.expect_equiv (Equiv.addLeft a)
        intro r
        rfl
      simp only [hshift, Fintype.expect_const]

theorem expect_independent_linear_evals [Fintype (E →ₗ[F2] F2)]
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) (g : R → F2 → ℚ) :
    (𝔼 X : E →ₗ[F2] R, 𝔼 ell : E →ₗ[F2] F2, g (X x) (ell x)) =
      𝔼 r : R, 𝔼 b : F2, g r b := by
  simp_rw [expect_linear_eval τ x hx]
  exact expect_linear_eval τ x hx (fun r => 𝔼 b : F2, g r b)

end Evaluation

open ActualSource

section Noise
variable {E : Type*} [AddCommGroup E] [Module F2 E] {s d : Nat}
  [Fintype (E →ₗ[F2] Ambient s d)] [Fintype (E →ₗ[F2] F2)]

noncomputable def localNoiseFailure (g : SplitGadget s d) (x : E) : ℚ :=
  𝔼 X : E →ₗ[F2] Ambient s d, 𝔼 i : g.NoiseIndex, 𝔼 ell : E →ₗ[F2] F2,
    if g.f (X x + ell x • g.noise i) = g.f (X x) then 0 else 1

theorem localNoiseFailure_eq_half (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x = g.stabilityError / 2 := by
  classical
  have hbit (r v : Ambient s d) :
      (𝔼 b : F2, if g.f (r + b • v) = g.f r then (0 : ℚ) else 1) =
        (if g.f (r + v) = g.f r then (0 : ℚ) else 1) / 2 := by
    have huniv : (Finset.univ : Finset F2) = {0, 1} := by decide
    by_cases h : g.f (r + v) = g.f r <;> simp [Finset.expect, huniv, h]
  have hinner (X : E →ₗ[F2] Ambient s d) (i : g.NoiseIndex) :
      (𝔼 ell : E →ₗ[F2] F2,
        if g.f (X x + ell x • g.noise i) = g.f (X x) then (0 : ℚ) else 1) =
      (if g.f (X x + g.noise i) = g.f (X x) then (0 : ℚ) else 1) / 2 := by
    exact (expect_linear_eval τ x hx
      (fun b => if g.f (X x + b • g.noise i) = g.f (X x) then (0 : ℚ) else 1)).trans
      (hbit (X x) (g.noise i))
  unfold localNoiseFailure
  simp_rw [hinner]
  rw [expect_linear_eval τ x hx (fun r => 𝔼 i : g.NoiseIndex,
    (if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1) / 2)]
  have hstab : g.stabilityError = 𝔼 r : Ambient s d, 𝔼 i : g.NoiseIndex,
      if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1 := by
    exact (Finset.expect_product Finset.univ Finset.univ
      (fun ri : Ambient s d × g.NoiseIndex =>
        if g.f (ri.1 + g.noise ri.2) = g.f ri.1 then (0 : ℚ) else 1))
  rw [hstab]
  simp only [div_eq_mul_inv]
  simp_rw [Finset.expect_mul]

theorem localNoiseFailure_le (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x ≤ g.stabilityError := by
  rw [localNoiseFailure_eq_half g τ x hx]
  have := g.stabilityError_nonneg
  linarith

end Noise

section Source

theorem expect_function_apply {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (j : I) (f : Ω → ℚ) :
    (𝔼 U : I → Ω, f (U j)) = 𝔼 w : Ω, f w := by
  classical
  calc
    (𝔼 U : I → Ω, f (U j)) =
        𝔼 p : Ω × ({j' : I // j' ≠ j} → Ω), f p.1 := by
      apply Fintype.expect_equiv (Equiv.funSplitAt j Ω)
      intro U
      rfl
    _ = 𝔼 w : Ω, f w := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

noncomputable def tupleFailure (S : Source) (A : Fin S.«variables» → Bool) (k : Nat) : ℚ :=
  𝔼 U : Fin k → Fin S.occurrences,
    if ∀ j, S.satisfied A (U j) = true then 0 else 1

theorem tupleFailure_le (S : Source) (A : Fin S.«variables» → Bool) (k : Nat) :
    tupleFailure S A k ≤ k * S.failure A := by
  classical
  have hpoint (U : Fin k → Fin S.occurrences) :
      (if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) ≤
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 := by
    by_cases hgood : ∀ j, S.satisfied A (U j) = true
    · simp [hgood]
    · have hex : ∃ j, S.satisfied A (U j) ≠ true := not_forall.mp hgood
      obtain ⟨j, hj⟩ := hex
      have hsum := Finset.single_le_sum
        (f := fun j : Fin k => if S.satisfied A (U j) then (0 : ℚ) else 1)
        (s := Finset.univ) (a := j) (by intro i _; split <;> norm_num)
        (Finset.mem_univ j)
      simpa [hgood, hj] using hsum
  calc
    tupleFailure S A k ≤ 𝔼 U : Fin k → Fin S.occurrences,
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 :=
      Finset.expect_le_expect (fun U _ => hpoint U)
    _ = ∑ j : Fin k, 𝔼 U : Fin k → Fin S.occurrences,
        if S.satisfied A (U j) then (0 : ℚ) else 1 := Finset.expect_sum_comm _ _ _
    _ = k * S.failure A := by
      have hcoord (j : Fin k) :
          (𝔼 U : Fin k → Fin S.occurrences,
            if S.satisfied A (U j) then (0 : ℚ) else 1) = S.failure A :=
        expect_function_apply j (fun e => if S.satisfied A e then (0 : ℚ) else 1)
      simp_rw [hcoord]
      simp

end Source

section HonestEvaluation
open ActualCanonical ActualHomogeneous
variable {Name Id R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R] {k : Nat}

def evalTriple (names : Id → Fin 3 → Name) (A : Name → F2) (e : Id)
    (a : Fin 3 → R) : R := ∑ i, A (names e i) • a i

def evalRecord (names : Id → Fin 3 → Name) (A : Name → F2) : Record Name Id R → R
  | .blank => 0
  | .single n c => A n • c
  | .full e a => evalTriple names A e a

def evaluate (names : Id → Fin 3 → Name) (A : Name → F2)
    (d : Data k Name Id R) : R := d.1 + ∑ j, evalRecord names A (d.2 j)

theorem record_eval_normalized (names : Id → Fin 3 → Name) (A : Name → F2)
    (e : Id) (a : Fin 3 → R) :
    evalRecord names A (record names e a) = evalTriple names A e (ActualCanonical.normalize a) := by
  classical
  by_cases h01 : a 0 = a 1
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · by_cases h12 : a 1 = a 2
      · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
          Fin.sum_univ_three, ActualCanonical.add_self]
      · simp [record, h01, h02, h12, evalRecord]

theorem record_eval_adjustment (names : Id → Fin 3 → Name) (A : Name → F2)
    (rhs : Id → F2) (e : Id) (a : Fin 3 → R)
    (hvalid : ∑ i, A (names e i) = rhs e) :
    rhs e • pivot a + evalRecord names A (record names e a) = evalTriple names A e a := by
  rw [record_eval_normalized]
  simp only [evalTriple, ActualCanonical.normalize, ActualCanonical.translate, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, hvalid]
  calc
    _ = (∑ i, A (names e i) • a i) + (rhs e • pivot a + rhs e • pivot a) := by abel
    _ = _ := by rw [ActualCanonical.add_self, add_zero]

theorem evaluate_data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (z : R) (a : Fin k → Fin 3 → R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (data occ names rhs z a) =
      z + ∑ j, evalTriple names A (occ j) (a j) := by
  simp only [evaluate, data]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => record_eval_adjustment names A rhs (occ j) (a j) (hvalid j))

def honestPoint (occ : Fin k → Id) (names : Id → Fin 3 → Name) (A : Name → F2) : E k :=
  (1, fun j => (A (names (occ j) 0), A (names (occ j) 1)))

@[simp] theorem honestPoint_tau (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (A : Name → F2) : tau (honestPoint occ names A) = 1 := rfl

theorem canonical_evaluate (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (X : E k →ₗ[F2] R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (canonical occ names rhs X) = X (honestPoint occ names A) := by
  rw [canonical, evaluate_data occ names rhs A _ _ hvalid]
  conv_rhs => rw [ActualHomogeneous.linearMap_expansion]
  simp [honestPoint, evalTriple, standardTriple, Fin.sum_univ_three]

end HonestEvaluation

section ActualLabeling
noncomputable section

def honestVertexLabel (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (v : ActualGame.Vertex S k s d) : Alphabet s :=
  g.f ((0, v.val.1) + ∑ j, evalRecord (ActualGame.names S)
    (fun n => ofBit (A n)) (v.val.2 j))

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => honestVertexLabel S k g A)

theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (ActualGame.canonical S k s d q)) := by
  simp only [honestLabeling, ActualGame.unfolded, ActualGame.sideLabel_labelingOf,
    ActualOrbit.unfold]
  let z := (ActualGame.canonical S k s d q).1
  let r := ∑ j, evalRecord (ActualGame.names S) (fun n => ofBit (A n))
    ((ActualGame.canonical S k s d q).2 j)
  change g.f ((0, z.2) + r) + z.1 = g.f (z + r)
  have hsplit : ((0, z.2) + r) + (z.1, 0) = z + r := by
    apply Prod.ext <;> simp [add_comm]
  have h := g.equivariant ((0, z.2) + r) z.1
  rw [hsplit] at h
  exact h.symm

def sourcePoint (S : Source) (k : Nat) (A : Fin S.«variables» → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.E k :=
  honestPoint U (ActualGame.names S) (fun n => ofBit (A n))

@[simp] theorem sourcePoint_tau (S : Source) (k : Nat) (A : Fin S.«variables» → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.tau (sourcePoint S k A U) = 1 := rfl

theorem satisfied_parity (S : Source) (A : Fin S.«variables» → Bool)
    (e : Fin S.occurrences) (h : S.satisfied A e = true) :
    ∑ i : Fin 3, ofBit (A (ActualGame.names S e i)) = ActualGame.rhs S e := by
  have hb : ((A (S.equation e).first ^^ A (S.equation e).second) ^^
      A (S.equation e).third) = (S.equation e).rhs := by
    simpa [Source.satisfied, CloneGap.satisfied] using h
  have hf := congrArg ofBit hb
  simpa [Fin.sum_univ_three, ActualGame.names, ActualGame.rhs, ofBit_xor, add_assoc]
    using hf

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (q.2 (sourcePoint S k A q.1)) := by
  rw [honest_unfolded]
  apply congrArg g.f
  exact canonical_evaluate q.1 (ActualGame.names S) (ActualGame.rhs S)
    (fun n => ofBit (A n)) q.2 (fun j => satisfied_parity S A (q.1 j) (hgood j))

private theorem expect_pair_inline_ActualCompleteness {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    (𝔼 p : I × J, f p) = 𝔼 i : I, 𝔼 j : J, f (i, j) :=
  Finset.expect_product _ _ _

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  classical
  let P (ω : ActualGame.Outcome S k g) : Prop :=
    ActualGame.unfolded S k s d (honestLabeling S k g A) false
        (ActualGame.leftQuery S k g ω) =
      ActualGame.unfolded S k s d (honestLabeling S k g A) true
        (ActualGame.rightQuery S k g ω)
  let bad (ω : ActualGame.Outcome S k g) : ℚ :=
    if ∀ j, S.satisfied A (ω.1.1 j) = true then 0 else 1
  let noiseBad (ω : ActualGame.Outcome S k g) : ℚ :=
    if g.f (ω.1.2 (sourcePoint S k A ω.1.1) +
        ω.2.2 (sourcePoint S k A ω.1.1) • g.noise ω.2.1) =
      g.f (ω.1.2 (sourcePoint S k A ω.1.1)) then 0 else 1
  have hpoint (ω : ActualGame.Outcome S k g) :
      (if P ω then (0 : ℚ) else 1) ≤ bad ω + noiseBad ω := by
    by_cases hgood : ∀ j, S.satisfied A (ω.1.1 j) = true
    · have hL := honest_unfolded_valid S k g A false (ActualGame.leftQuery S k g ω) hgood
      have hR := honest_unfolded_valid S k g A true (ActualGame.rightQuery S k g ω) hgood
      simp only [P, hL, hR, bad, ite_eq_left hgood, zero_add]
      simp [noiseBad, ActualGame.leftQuery, ActualGame.rightQuery,
        LinearMap.add_apply, LinearMap.smulRight_apply, eq_comm]
      exact le_rfl
    · have hn : 0 ≤ noiseBad ω := by dsimp [noiseBad]; split <;> norm_num
      have hf : (if P ω then (0 : ℚ) else 1) ≤ 1 := by split <;> norm_num
      simpa only [bad, ite_eq_right hgood] using hf.trans (le_add_of_nonneg_right hn)
  have hbad : (𝔼 ω : ActualGame.Outcome S k g, bad ω) = tupleFailure S A k := by
    simp only [expect_pair_inline_ActualCompleteness, bad]
    change (𝔼 U : ActualGame.Question S k, 𝔼 _X : ActualGame.Map k s d,
      𝔼 _i : g.NoiseIndex, 𝔼 _ell : ActualGame.Dual k,
      if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) = _
    simp_rw [Fintype.expect_const]
    rfl
  have hnoise : (𝔼 ω : ActualGame.Outcome S k g, noiseBad ω) = g.stabilityError / 2 := by
    simp only [expect_pair_inline_ActualCompleteness]
    change (𝔼 U : ActualGame.Question S k, localNoiseFailure g (sourcePoint S k A U)) = _
    have hu (U : ActualGame.Question S k) := localNoiseFailure_eq_half g
      ActualHomogeneous.tau (sourcePoint S k A U) (sourcePoint_tau S k A U)
    simp only [hu, Fintype.expect_const]
  have hfailure : (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) ≤
      tupleFailure S A k + g.stabilityError / 2 := by
    calc
      _ ≤ 𝔼 ω : ActualGame.Outcome S k g, (bad ω + noiseBad ω) :=
        Finset.expect_le_expect (fun ω _ => hpoint ω)
      _ = _ := by rw [Finset.expect_add_distrib, hbad, hnoise]
  have hsum : ActualGame.acceptanceProbability S k g (honestLabeling S k g A) +
      (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) = 1 := by
    rw [ActualGame.acceptanceProbability_eq_test]
    change (𝔼 ω : ActualGame.Outcome S k g, if P ω then (1 : ℚ) else 0) + _ = _
    rw [← Finset.expect_add_distrib]
    have hp (ω : ActualGame.Outcome S k g) :
        (if P ω then (1 : ℚ) else 0) + (if P ω then (0 : ℚ) else 1) = 1 := by
      split <;> norm_num
    simp only [hp, Fintype.expect_const]
  have htuple := tupleFailure_le S A k
  linarith

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (γ η ε : ℚ)
    (hsource : S.failure A ≤ γ) (hstable : g.stabilityError ≤ η)
    (hbudget : (k : ℚ) * γ + η / 2 ≤ ε) :
    1 - ε ≤ ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

theorem honest_satisfied_fraction_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      (Foundations.Target.countSatisfied (honestLabeling S k g A)
        (ActualGame.outputInstance S k g).constraints : ℚ) /
        (ActualGame.outputInstance S k g).constraints.length := by
  rw [← ActualGame.acceptanceProbability_eq_count]
  exact honest_acceptance_bound S k g A

theorem actual_completeAt (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool)
    (error : Foundations.Target.RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    Foundations.Target.CompleteAt error (ActualGame.outputInstance S k g) := by
  apply (Integration.GapSemantics.completeAt_iff error _).2
  refine ⟨honestLabeling S k g A, ?_⟩
  change 1 - Integration.GapSemantics.errorValue error ≤
    (Foundations.Target.countSatisfied (honestLabeling S k g A)
      (ActualGame.outputInstance S k g).constraints : ℚ) /
      (ActualGame.outputInstance S k g).constraints.length
  have h := honest_satisfied_fraction_bound S k g A
  linarith

end
end ActualLabeling

end DFVSGames.Reduction.ActualCompleteness
end

section

namespace DFVSGames.Decoder.TableKeysCompleteness

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

def diagonalLabeling (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => vertexLabel S k s d labeling)

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) : Fin (vertexCount S k s d) → Fin (2^s) :=
  labelingOf S k s d (ActualCompleteness.honestVertexLabel S k g A)

theorem diagonal_honestLabeling (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    diagonalLabeling S k s d (honestLabeling S k g A) =
      ActualCompleteness.honestLabeling S k g A := by
  simp only [diagonalLabeling, honestLabeling, vertexLabel_labelingOf,
    ActualCompleteness.honestLabeling]

theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (q : Query S k s d) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (ActualCompleteness.evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (canonical S k s d q)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded S k g A false q

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (q : Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (q.2 (ActualCompleteness.sourcePoint S k A q.1)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded_valid S k g A false q hgood

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

theorem honest_satisfied_fraction_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      (countSatisfied (honestLabeling S k g A)
        (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [← acceptanceProbability_eq_count]
  exact honest_acceptance_bound S k g A

theorem completeAt (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstance S k g) := by
  apply (Integration.GapSemantics.completeAt_iff error _).2
  refine ⟨honestLabeling S k g A, ?_⟩
  change 1 - Integration.GapSemantics.errorValue error ≤
    (countSatisfied (honestLabeling S k g A)
      (outputInstance S k g).constraints : ℚ) /
      (outputInstance S k g).constraints.length
  have h := honest_satisfied_fraction_bound S k g A
  linarith

theorem completeAt_withEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (A : Fin S.«variables» → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstanceWithEnumeration S k g en) := by
  apply (completeAt_outputInstanceWithEnumeration_iff error S k g en).2
  exact completeAt S k g A error hbudget

end

end DFVSGames.Decoder.TableKeysCompleteness
end

section

namespace DFVSGames.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

abbrev Ambient (s d : Nat) := Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d
abbrev Record (n m s d : Nat) := ActualCanonical.Record (Fin n) (Fin m) (Ambient s d)
abbrev Body (n m k s d : Nat) := Integration.BinaryLinear.Vector d × (Fin k → Record n m s d)

def vectorWord {s : Nat} (v : Integration.BinaryLinear.Vector s) : Nat :=
  (Encoding.alphabetEquiv s v).val

theorem vectorWord_lt {s : Nat} (v : Integration.BinaryLinear.Vector s) :
    vectorWord v < 2^s := (Encoding.alphabetEquiv s v).isLt

theorem vectorWord_injective {s : Nat} :
    Function.Injective (vectorWord (s := s)) := by
  intro x y h
  apply (Encoding.alphabetEquiv s).injective
  exact Fin.ext h

@[simp] theorem vectorWord_eq_iff {s : Nat} (x y : Integration.BinaryLinear.Vector s) :
    vectorWord x = vectorWord y ↔ x = y := vectorWord_injective.eq_iff

def recordWords {n m s d : Nat} : Record n m s d → List Nat
  | .blank => [0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .single name coefficient =>
      [1, name.val, 0, vectorWord coefficient.1, vectorWord coefficient.2, 0, 0, 0, 0]
  | .full occurrence coefficients =>
      [2, 0, occurrence.val,
        vectorWord (coefficients 0).1, vectorWord (coefficients 0).2,
        vectorWord (coefficients 1).1, vectorWord (coefficients 1).2,
        vectorWord (coefficients 2).1, vectorWord (coefficients 2).2]

@[simp] theorem recordWords_length {n m s d : Nat} (r : Record n m s d) :
    (recordWords r).length = 9 := by
  cases r <;> rfl

theorem recordWords_injective {n m s d : Nat} :
    Function.Injective (recordWords (n := n) (m := m) (s := s) (d := d)) := by
  intro r t h
  cases r with
  | blank => cases t <;> simp_all [recordWords]
  | single name coefficient =>
    cases t with
    | blank => simp [recordWords] at h
    | single name' coefficient' =>
      simp [recordWords] at h
      rcases h with ⟨hn, hc, hd⟩
      have hp : coefficient = coefficient' := Prod.ext hc hd
      have hn' : name = name' := Fin.ext hn
      cases hn'
      cases hp
      rfl
    | full occurrence coefficients => simp [recordWords] at h
  | full occurrence coefficients =>
    cases t with
    | blank => simp [recordWords] at h
    | single name coefficient => simp [recordWords] at h
    | full occurrence' coefficients' =>
      simp [recordWords] at h
      rcases h with ⟨hi, h0c, h0d, h1c, h1d, h2c, h2d⟩
      have hp : coefficients = coefficients' := by
        funext i
        fin_cases i
        · exact Prod.ext h0c h0d
        · exact Prod.ext h1c h1d
        · exact Prod.ext h2c h2d
      have hi' : occurrence = occurrence' := Fin.ext hi
      cases hi'
      cases hp
      rfl

def recordsWords {n m s d : Nat} (rs : List (Record n m s d)) : List Nat :=
  rs.flatMap recordWords

@[simp] theorem recordsWords_nil {n m s d : Nat} :
    recordsWords ([] : List (Record n m s d)) = [] := rfl

@[simp] theorem recordsWords_cons {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    recordsWords (r :: rs) = recordWords r ++ recordsWords rs := rfl

@[simp] theorem recordsWords_length {n m s d : Nat} (rs : List (Record n m s d)) :
    (recordsWords rs).length = 9 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem recordsWords_take_head {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    (recordsWords (r :: rs)).take 9 = recordWords r := by
  change (recordWords r ++ recordsWords rs).take 9 = recordWords r
  simpa only [recordWords_length] using
    (List.take_append_length (l₁ := recordWords r) (l₂ := recordsWords rs))

theorem recordsWords_injective {n m s d : Nat} :
    Function.Injective (recordsWords (n := n) (m := m) (s := s) (d := d)) := by
  intro rs
  induction rs with
  | nil =>
    intro ts h
    cases ts with
    | nil => rfl
    | cons t ts =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
  | cons r rs ih =>
    intro ts h
    cases ts with
    | nil =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
    | cons t ts =>
      have hh := congrArg (List.take 9) h
      simp only [recordsWords_take_head] at hh
      have hr := recordWords_injective hh
      subst t
      apply congrArg (List.cons r)
      apply ih
      exact List.append_cancel_left (by simpa only [recordsWords_cons] using h)

def bodyWords {n m k s d : Nat} (body : Body n m k s d) : List Nat :=
  vectorWord body.1 :: recordsWords (List.ofFn body.2)

@[simp] theorem bodyWords_length {n m k s d : Nat} (body : Body n m k s d) :
    (bodyWords body).length = 1 + 9*k := by
  simp [bodyWords, Nat.add_comm]

theorem bodyWords_injective {n m k s d : Nat} :
    Function.Injective (bodyWords (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  have hh := List.cons.inj h
  apply Prod.ext
  · exact vectorWord_injective hh.1
  · exact List.ofFn_injective (recordsWords_injective hh.2)

@[simp] theorem bodyWords_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyWords x = bodyWords y ↔ x = y := bodyWords_injective.eq_iff

def wordBound (n m s d : Nat) : Nat := n + m + 2^s + 2^d + 3

theorem recordWords_bounded {n m s d : Nat} (r : Record n m s d)
    (w : Nat) (hw : w ∈ recordWords r) : w ≤ wordBound n m s d := by
  unfold wordBound
  cases r with
  | blank =>
    simp [recordWords] at hw
    subst w
    exact Nat.zero_le _
  | single name coefficient =>
    have hn := name.isLt
    have hc := vectorWord_lt coefficient.1
    have hd := vectorWord_lt coefficient.2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega
  | full occurrence coefficients =>
    have hi := occurrence.isLt
    have h0c := vectorWord_lt (coefficients 0).1
    have h0d := vectorWord_lt (coefficients 0).2
    have h1c := vectorWord_lt (coefficients 1).1
    have h1d := vectorWord_lt (coefficients 1).2
    have h2c := vectorWord_lt (coefficients 2).1
    have h2d := vectorWord_lt (coefficients 2).2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega

theorem bodyWords_bounded {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w ≤ wordBound n m s d := by
  rcases List.mem_cons.mp hw with h | h
  · subst w
    have hv := vectorWord_lt body.1
    have hs : 0 < (2 : Nat)^s := pow_pos (by decide) _
    unfold wordBound
    omega
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
    exact recordWords_bounded r w hr

def bodyBits {n m k s d : Nat} (body : Body n m k s d) : List Bool :=
  encodeWords (bodyWords body)

theorem bodyBits_injective {n m k s d : Nat} :
    Function.Injective (bodyBits (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  exact bodyWords_injective (encodeWords_injective h)

@[simp] theorem bodyBits_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyBits x = bodyBits y ↔ x = y := bodyBits_injective.eq_iff

theorem bodyBits_length_le {n m k s d : Nat} (body : Body n m k s d) :
    (bodyBits body).length ≤ (1 + 9*k) * (n + m + 2^s + 2^d + 4) := by
  simpa only [bodyBits, bodyWords_length, wordBound, Nat.add_assoc] using
    encodeWords_length_le (bodyWords body) (wordBound n m s d) (bodyWords_bounded body)

theorem imageVertices_bodyWords {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d) :
    Encoding.imageVertices queries (fun q => bodyWords (body q)) =
      (Encoding.imageVertices queries body).map bodyWords := by
  unfold Encoding.imageVertices
  simpa only [List.map_map, Function.comp_def] using
    List.dedup_map_of_injective bodyWords_injective (queries.map body)

theorem imageVertices_bodyBits {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d) :
    Encoding.imageVertices queries (fun q => bodyBits (body q)) =
      (Encoding.imageVertices queries body).map bodyBits := by
  unfold Encoding.imageVertices
  simpa only [List.map_map, Function.comp_def] using
    List.dedup_map_of_injective bodyBits_injective (queries.map body)

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (x : A) (xs : List A) :
    (xs.map f).idxOf (f x) = xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y = x
    · subst y
      simp
    · have h' : f y ≠ f x := fun hxy => h (hf hxy)
      simp [h, h', ih]

theorem imageIndex_map_val {Q A B : Type*} [DecidableEq A] [DecidableEq B]
    (queries : List Q) (body : Q → A) (f : A → B) (hf : Function.Injective f)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => f (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val := by
  change ((queries.map (fun q => f (body q))).dedup).idxOf (f (body q)) =
    ((queries.map body).dedup).idxOf (body q)
  have hmap : (queries.map (fun q => f (body q))).dedup =
      (queries.map body).dedup.map f := by
    simpa only [List.map_map, Function.comp_def] using
      List.dedup_map_of_injective hf (queries.map body)
  rw [hmap]
  exact idxOf_map_injective f hf (body q) (queries.map body).dedup

theorem imageIndex_bodyWords_val {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => bodyWords (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val :=
  imageIndex_map_val queries body bodyWords bodyWords_injective q hq

theorem imageIndex_bodyBits_val {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => bodyBits (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val :=
  imageIndex_map_val queries body bodyBits bodyBits_injective q hq

end DFVSGames.Reduction.CanonicalEncoding
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
