import Mathlib
import OAI.Computability.MaxCut.Encoding.SelectedPolicies

namespace OAI

namespace MaxCutGames.Decoder.VisibleTransfer

open MaxCutGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

/-- The part of an event in one actual visible-data fiber. -/
def fiberEvent (observe : Ω → D) (d : D) (event : Ω → Bool) : Ω → Bool := by
  classical
  exact fun x => decide (observe x = d) && event x

def fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : ℝ :=
  μ.probability (fiberEvent observe d event)

omit [Fintype D] in
theorem fiberMass_nonnegative (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : 0 ≤ fiberMass μ observe d event :=
  μ.probability_nonnegative _

omit [Fintype D] in
theorem fiberMass_mono (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    fiberMass μ observe d event ≤ fiberMass μ observe d event' := by
  apply μ.probability_mono
  intro x hx
  simp only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, h x hx.2⟩

theorem sum_fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (event : Ω → Bool) :
    ∑ d, fiberMass μ observe d event = μ.probability event := by
  classical
  unfold fiberMass FiniteDistribution.probability fiberEvent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases event x <;> simp

theorem observation_weight (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D) :
    (μ.pushforward observe).weight d = fiberMass μ observe d (fun _ => true) := by
  classical
  simp [FiniteDistribution.pushforward, fiberMass, FiniteDistribution.probability,
    fiberEvent]

/-- Positive projected column-slice mass and sufficient conditional target
agreement. Both quantities are computed after fixing actual visible data. -/
def visibleWitness (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D) : Bool := by
  classical
  exact decide (0 < fiberMass μ observe d slice ∧
    threshold * fiberMass μ observe d slice ≤
      fiberMass μ observe d (fun x => slice x && targetHit x))

/-- The positive part of the witness margin is paid for by the probability of
the actual observed data, rather than by the larger hidden sample space. -/
theorem witness_margin_le_visible_probability
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice ≤
      (μ.pushforward observe).probability (visibleWitness μ observe slice targetHit threshold) := by
  classical
  have pointwise (d : D) :
      fiberMass μ observe d (fun x => slice x && targetHit x) -
          threshold * fiberMass μ observe d slice ≤
        if visibleWitness μ observe slice targetHit threshold d then
          (μ.pushforward observe).weight d else 0 := by
    have hs := fiberMass_nonnegative μ observe d slice
    have hm := fiberMass_nonnegative μ observe d (fun x => slice x && targetHit x)
    have hms : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        fiberMass μ observe d slice := by
      apply fiberMass_mono
      intro x hx
      simp only [Bool.and_eq_true] at hx
      exact hx.1
    have hmo : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        (μ.pushforward observe).weight d := by
      rw [observation_weight]
      exact fiberMass_mono μ observe d (fun _ _ => rfl)
    by_cases hgood : visibleWitness μ observe slice targetHit threshold d = true
    · simp only [hgood, ↓reduceIte]
      exact (sub_le_self _ (mul_nonneg hthreshold hs)).trans hmo
    · simp only [hgood, Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 0 < fiberMass μ observe d slice
      · have hnot : ¬ threshold * fiberMass μ observe d slice ≤
            fiberMass μ observe d (fun x => slice x && targetHit x) := by
          intro hle
          exact hgood (by simp [visibleWitness, hpos, hle])
        linarith
      · have hzero : fiberMass μ observe d slice = 0 := le_antisymm (le_of_not_gt hpos) hs
        rw [hzero, mul_zero, sub_zero]
        exact hms.trans_eq hzero
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun d _ => pointwise d
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fiberMass,
    FiniteDistribution.probability] using hsum

omit [Fintype D] in
/-- On every selected datum the conditional distribution is defined on an
actual nonempty positive-mass slice and has the promised target agreement. -/
theorem visibleWitness_conditional
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D)
    (h : visibleWitness μ observe slice targetHit threshold d = true) :
    ∃ hpositive : 0 < μ.probability (fiberEvent observe d slice),
      threshold ≤ (μ.condition (fiberEvent observe d slice) hpositive).probability targetHit := by
  classical
  have hh : 0 < fiberMass μ observe d slice ∧
      threshold * fiberMass μ observe d slice ≤
        fiberMass μ observe d (fun x => slice x && targetHit x) := by
    simpa only [visibleWitness, decide_eq_true_eq] using h
  unfold fiberMass at hh
  refine ⟨hh.1, ?_⟩
  rw [FiniteDistribution.probability_condition]
  have hsame : (fun x => fiberEvent observe d slice x && targetHit x) =
      fiberEvent observe d (fun x => slice x && targetHit x) := by
    funext x
    simp [fiberEvent, Bool.and_assoc]
  rw [hsame]
  exact (le_div_iff₀ hh.1).mpr hh.2

omit [Fintype D] in
/-- Goodness is inherited from any event whose membership requires good
visible advice. Positivity supplies an actual supporting hidden sample. -/
theorem visibleWitness_good
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ)
    (good : D → Prop) (hslice : ∀ x, slice x = true → good (observe x))
    (d : D) (h : visibleWitness μ observe slice targetHit threshold d = true) :
    good d := by
  classical
  have hpos : 0 < fiberMass μ observe d slice := by
    have hh := of_decide_eq_true h
    exact hh.1
  by_contra hbad
  have hempty : fiberEvent observe d slice = fun _ => false := by
    funext x
    apply Bool.eq_false_iff.mpr
    intro hx
    have hh : observe x = d ∧ slice x = true := by
      simpa only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
    exact hbad (hh.1 ▸ hslice x hh.2)
  unfold fiberMass at hpos
  rw [hempty, FiniteDistribution.probability_false] at hpos
  exact (lt_irrefl 0) hpos

/-- A pair of full-table event probabilities transfers with error
`(1 + threshold) * TV`. This estimate precedes all conditioning. -/
theorem margin_transfer (μ ν : FiniteDistribution Ω)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice -
        (1 + threshold) * μ.totalVariation ν ≤
      ν.probability (fun x => slice x && targetHit x) - threshold * ν.probability slice := by
  have hm := μ.probability_sub_le_totalVariation ν (fun x => slice x && targetHit x)
  have hs := ν.probability_sub_le_totalVariation μ slice
  rw [FiniteDistribution.totalVariation_comm] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hthreshold
  nlinarith

/-- The whole-table comparison and the exact finite disintegration combine
without any assumption on conditional projection laws. -/
theorem wholeTable_transfer_to_visibleWitness
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (threshold γ : ℝ) (hthreshold : 0 ≤ threshold)
    (hmargin : γ ≤
      unrestricted.probability (fun x => slice x && targetHit x) -
        threshold * unrestricted.probability slice -
        (1 + threshold) * unrestricted.totalVariation (actual.pushforward pad)) :
    γ ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) threshold) := by
  have transferred := margin_transfer unrestricted (actual.pushforward pad)
    slice targetHit threshold hthreshold
  simp only [FiniteDistribution.probability_pushforward] at transferred
  exact (hmargin.trans transferred).trans
    (witness_margin_le_visible_probability actual observe
      (fun x => slice (pad x)) (fun x => targetHit (pad x)) threshold hthreshold)

theorem projected_witness_mass
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (α g₀ c : ℝ) (hα : 0 ≤ α)
    (hslice : g₀ * c ≤ unrestricted.probability slice)
    (hagreement : (α / 2) * unrestricted.probability slice ≤
      unrestricted.probability (fun x => slice x && targetHit x))
    (herror : (1 + α / 4) * unrestricted.totalVariation (actual.pushforward pad) ≤
      α * g₀ * c / 8) :
    α * g₀ * c / 8 ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) (α / 4)) := by
  apply wholeTable_transfer_to_visibleWitness unrestricted actual pad observe slice targetHit
    (α / 4) (α * g₀ * c / 8) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hslice (show 0 ≤ α / 4 by positivity)
  nlinarith

end
end MaxCutGames.Decoder.VisibleTransfer

namespace MaxCutGames.Decoder.UniformFibers

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

def selectedFiberEquiv (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d}) :
    {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true} ≃
      {y : Y // slice (e y).val = true} where
  toFun x := by
    have hx : observe x.val = d ∧ slice x.val = true := by
      simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using x.property
    refine ⟨e.symm ⟨x.val, hx.1⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hx.2
  invFun y := ⟨(e y.val).val, by
    simp only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(e y.val).property, y.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    exact e.symm_apply_apply y.val

theorem selectedFiberEquiv_point (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d})
    (x : {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true}) :
    (e (selectedFiberEquiv observe d slice e x).val).val = x.val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Conditioning after fixing the complete datum and the selected column
event leaves precisely the uniform restricted private fiber. -/
theorem conditional_probability [Fintype Ω] [Fintype Y]
    (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D)
    (slice event : Ω → Bool)
    (positive : 0 < μ.probability (VisibleTransfer.fiberEvent observe d slice))
    (c : ℝ) (hconstant : ∀ x, observe x = d → μ.weight x = c)
    (e : Y ≃ {x : Ω // observe x = d}) :
    (μ.condition (VisibleTransfer.fiberEvent observe d slice) positive).probability event =
      𝔼 y : {y : Y // slice (e y).val = true},
        if event (e y.val).val then (1 : ℝ) else 0 := by
  apply UniformConditioning.condition_probability_equiv μ
    (VisibleTransfer.fiberEvent observe d slice) event positive c
    (fun x hx => hconstant x (by
      have h : observe x = d ∧ slice x = true := by
        simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
      exact h.1))
    (selectedFiberEquiv observe d slice e)
    (fun y => event (e y.val).val)
  intro x
  rw [selectedFiberEquiv_point]

end
end MaxCutGames.Decoder.UniformFibers

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace MaxCutGames.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

section Conditioning

variable {k : ℕ} {Id K W R : Type}
    [Fintype Id] [AddCommGroup K] [Module F2 K] [Fintype K]
    [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup R] [Module F2 R] [Fintype R]

theorem probability_condition_complete
    (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (d : AdviceLaw.CompleteData k Id K W R)
    (slice event : AdviceLaw.FullSeed k Id K W R → Bool)
    (positive : 0 < (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice)) :
    ((AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice) positive).probability event =
        𝔼 N : {N : AdviceLaw.PrivateMap d // slice (AdviceLaw.completeAssemble d N) = true},
          if event (AdviceLaw.completeAssemble d N.val) then (1 : ℝ) else 0 := by
  exact UniformFibers.conditional_probability
    (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ')
    AdviceLaw.completeObserve d slice event positive
    (AdviceLaw.completeWeight occurrences publicLaw β d)
    (AdviceLaw.fullSeed_weight_fiber occurrences publicLaw β hβ hβ' d)
    (AdviceLaw.completeFiberEquiv d)

end Conditioning

variable {k s d r : ℕ}

/-- Both provers' answers, and their equality predicate, are fixed on the
complete observation fiber. Only the hidden matrix varies within that fiber. -/
theorem observedAgreement_completeDraw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (N N' : AdviceLaw.PrivateMap data) :
    VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N) =
      VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N') := by
  unfold VisiblePolicies.observedAgreement
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]
  simp only [AdviceExperiment.rightObservation, AdviceLaw.completeDraw_rows]
  rfl

def datumAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data 0)

theorem datumAgreement_nonneg (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    0 ≤ datumAgreement S labeling good data :=
  FiniteDistribution.probability_nonnegative _ _

/-- The actual success observable factors through the complete visible datum;
this justifies integrating a lower bound over visible-witness probability. -/
theorem observedAgreement_seed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (x : AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    VisiblePolicies.observedAgreement S labeling good
      (AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2) =
        datumAgreement S labeling good (AdviceLaw.completeObserve x) := by
  let y := AdviceLaw.fullSeedCoordinatesEquiv x
  have hx : AdviceLaw.completeAssemble y.1 y.2 = x :=
    AdviceLaw.fullSeedCoordinatesEquiv.symm_apply_apply x
  rw [← hx, AdviceLaw.completeDraw_seed]
  change VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw y.1 y.2) =
    datumAgreement S labeling good (AdviceLaw.completeObserve (AdviceLaw.completeAssemble y.1 y.2))
  rw [AdviceLaw.completeObserve_assemble]
  exact observedAgreement_completeDraw S labeling good y.1 y.2 0

end
end MaxCutGames.Decoder.ActualConditionalLaw

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedFiberLaw

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse MaxCutGames.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The universe finset is independent of the chosen finite enumeration.
The instances are explicit so elaboration need not unfold either enumeration. -/
private theorem univ_congr_inline_SelectedFiberLaw {X : Type*} (i j : Fintype X) :
    @Finset.univ X i = @Finset.univ X j := by
  cases Subsingleton.elim i j
  rfl

private theorem condition_prob_enumeration {Ω : Type} (i j : Fintype Ω)
    (μ : @FiniteDistribution Ω i) (ν : @FiniteDistribution Ω j)
    (hw : ∀ x, @FiniteDistribution.weight Ω i μ x = @FiniteDistribution.weight Ω j ν x) (slice event : Ω → Bool)
    (hm : 0 < @FiniteDistribution.probability Ω i μ slice)
    (hn : 0 < @FiniteDistribution.probability Ω j ν slice) :
    @FiniteDistribution.probability Ω i (@FiniteDistribution.condition Ω i μ slice hm) event =
      @FiniteDistribution.probability Ω j (@FiniteDistribution.condition Ω j ν slice hn) event := by
  cases Subsingleton.elim i j
  let : Fintype Ω := i
  have he : μ = ν := FiniteDistribution.eq_of_weight_eq hw
  subst ν
  rfl

variable {k s d r : ℕ}

def datumLeft (S : Source) (data : Datum S k s d r) : LeftInput S k s d (Vector r) :=
  AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

def datumMatrix (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :=
  (AdviceLaw.completeDraw data N).hiddenMatrix

def datumProjection (S : Source) (data : Datum S k s d r) :=
  AdviceExperiment.projection (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

theorem datumLeft_eq (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N) =
      datumLeft S data := by
  unfold datumLeft
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]

theorem datumMatrix_rows (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    data.1.2.comp (datumMatrix S data N) = data.2.2.2.val :=
  AdviceLaw.completeDraw_rows data N

theorem datumMatrix_rowAdvice (S : Source) (data : Datum S k s d r)
    (N : AdviceLaw.PrivateMap data) :
    RowErasureMatrix.rowAdvice (LinearMap.toMatrix' data.1.2)
        (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      mapEquiv k r (datumLeft S data).rows := by
  rw [← mapEquiv_rowAdvice]
  change mapEquiv k r ((data.1.2.comp (datumMatrix S data N)).comp (datumProjection S data)) =
    mapEquiv k r ((data.1.2.comp (datumMatrix S data 0)).comp (datumProjection S data))
  rw [datumMatrix_rows, datumMatrix_rows] ; rfl

/-- Every event membership uses the same selected normalized witness on the
entire complete-data fiber. -/
theorem slice_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data) :
    slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).toSlice.points := by
  rw [slice_eq_selectedEvent]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  exact SelectedDecoding.selectedEvent_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)

/-- On the selected event, the actual full-table target-hit predicate equals
projected affine equality with the very same normalized coefficient/intercept. -/
theorem target_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) =
        datumMatrix S data N (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept := by
  have hp := (slice_assemble_iff S labeling α hα hsmall data hgood N).mp hN
  rw [targetHit_eq_selectedMatch]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  refine (SelectedDecoding.selectedMatch_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)).trans ?_
  have hp' : mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood) := hp
  simp only [hp', true_and, LinearEquiv.symm_apply_apply]
  rw [show fullTable S labeling (datumLeft S data)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) from
    ProjectedColumnSlice.fullTable_padded S labeling (AdviceLaw.completeDraw data 0) (datumMatrix S data N)] ; rfl

/-- Positive mass supplies a supporting private coordinate in the selected
fiber; neither a hidden matrix nor good advice is an additional premise. -/
theorem exists_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ∃ N : AdviceLaw.PrivateMap data,
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true := by
  have hex : ∃ x : Seed S k s d r,
      VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α) x = true := by
    by_contra hn
    have he : VisibleTransfer.fiberEvent AdviceLaw.completeObserve data
        (slice S k s d r labeling α) = fun _ => false := by
      funext x
      apply Bool.eq_false_iff.mpr
      intro hx
      exact hn ⟨x, hx⟩
    rw [he, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨x, hx⟩ := hex
  have hx' : AdviceLaw.completeObserve x = data ∧ slice S k s d r labeling α x = true := by
    simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
  let N := (AdviceLaw.completeFiberEquiv data).symm ⟨x, hx'.1⟩
  have he : AdviceLaw.completeAssemble data N = x :=
    congrArg Subtype.val ((AdviceLaw.completeFiberEquiv data).apply_symm_apply ⟨x, hx'.1⟩)
  exact ⟨N, he.symm ▸ hx'.2⟩

theorem good_of_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    GoodAdvice S labeling α (datumLeft S data) := by
  have hg := slice_good S k s d r labeling α (AdviceLaw.completeAssemble data N) hN
  change GoodAdvice S labeling α
    (AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N)) at hg
  rw [datumLeft_eq] at hg
  exact hg

/-- The actual selected private coordinates are in bijection with the complete
projected affine slice. The supporting point is used only to state its column
equations; the canonical visible base still defines the private coordinates. -/
def selectedPrivateEquiv (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true) :
    {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} ≃
      RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) := by
  let D := normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood
  let e := AdviceFibers.rowFiberEquiv data.1.2 data.2.2.2.val
    (AdviceFibers.observedBase data.1.2 data.2.2.2)
    (AdviceFibers.observedBase_property data.1.2 data.2.2.2)
  have hs : mapEquiv k s ((datumMatrix S data Nstar).comp (datumProjection S data)) ∈ D.toSlice.points :=
    (slice_assemble_iff S labeling α hα hsmall data hgood Nstar).mp hstar
  have hrow (N : AdviceLaw.PrivateMap data) :
      data.1.2.comp (datumMatrix S data N) = data.1.2.comp (datumMatrix S data Nstar) := by
    rw [datumMatrix_rows, datumMatrix_rows]
  let lift := fun M : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) =>
    e.symm ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩
  have hlift (M) : datumMatrix S data (lift M) = M.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩)
  refine {
    toFun := fun N => ⟨datumMatrix S data N.val, hrow N.val, ?_⟩
    invFun := fun M => ⟨lift M, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs
      (datumMatrix S data N.val) (hrow N.val)).mp
        ((slice_assemble_iff S labeling α hα hsmall data hgood N.val).mp N.property)
  · apply (slice_assemble_iff S labeling α hα hsmall data hgood (lift M)).mpr
    rw [hlift]
    exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs M.val M.property.1).mpr M.property.2
  · intro N
    apply Subtype.ext
    exact e.symm_apply_apply N.val
  · intro M
    apply Subtype.ext
    exact hlift M

@[simp] theorem selectedPrivateEquiv_val (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (N : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true}) :
    (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar N).val =
      datumMatrix S data N.val := rfl

/-- Exact conditional target probability, with no assumed uniformity premise. -/
theorem conditional_eq_transferred (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ((law S k s d r β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))
        positive).probability (targetHit S k s d r labeling α) =
      SelectedDecoding.transferredAgreement S labeling (AdviceLaw.completeDraw data 0)
        (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood)
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        (datumMatrix S data Nstar) := by
  let : Fintype (Fin S.occurrences) := Fin.fintype _
  let : Fintype (Alphabet s) := @Pi.instFintype (Fin s) (fun _ => F2) (instDecidableEqFin s) (Fin.fintype s) (fun _ => ZMod.fintype 2)
  let : Fintype (Vector d) := @Pi.instFintype (Fin d) (fun _ => F2) (instDecidableEqFin d) (Fin.fintype d) (fun _ => ZMod.fintype 2)
  let : Fintype (Vector r) := @Pi.instFintype (Fin r) (fun _ => F2) (instDecidableEqFin r) (Fin.fintype r) (fun _ => ZMod.fintype 2)
  let : Fintype (Alphabet s →ₗ[F2] Vector r) := ActualConditionalLaw.homFintype
  unfold law at positive ⊢
  have hconditional := ActualConditionalLaw.probability_condition_complete
    (k := k) (Id := Fin S.occurrences) (K := Alphabet s) (W := Vector d) (R := Vector r)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ' data
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (by
      convert positive using 1
      simp only [FiniteDistribution.probability,
        AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform,
        ← Nat.card_eq_fintype_card]
      apply Finset.sum_congr (univ_congr_inline_SelectedFiberLaw _ _)
      intro x hx
      rfl)
  refine Eq.trans ?_ (hconditional.trans ?_)
  · apply condition_prob_enumeration
    intro x
    simp only [AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform,
      ← Nat.card_eq_fintype_card]
  ·
    let : Fintype (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask data.2.1) →ₗ[F2] Alphabet s) :=
      homFintype
    let : Fintype (RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar)) :=
      SelectedDecoding.affineSliceFintype _ _ _
    let f : {N : AdviceLaw.PrivateMap data //
        slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} → ℝ :=
      fun N => if targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N.val) = true
        then 1 else 0
    let g : RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) → ℝ :=
      fun M => if TableKeysRestoration.projectedAnswer S k s d labeling
          (PaddedLaw.choiceMask data.2.1)
          (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
            data.1.1 (PaddedLaw.choiceSlots data.2.1)) (M.val.prod data.2.2.1) =
          M.val (datumProjection S data
            (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
            (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        then 1 else 0
    have he : (𝔼 N, f N) = 𝔼 M, g M := by
      refine Fintype.expect_equiv
        (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar) f g ?_
      intro N
      dsimp only [f, g]
      simp only [selectedPrivateEquiv_val]
      exact TransferredDecoding.indicator_congr _ _ _ _
        (target_assemble_iff S labeling α hα hsmall data hgood N.val N.property)
    calc
      _ = 𝔼 N, f N := by
        apply Finset.expect_congr (by ext N; simp only [Finset.mem_univ])
        intro N _
        exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl
      _ = 𝔼 M, g M := he
      _ = _ := by
        unfold SelectedDecoding.transferredAgreement
        apply Finset.expect_congr (univ_congr_inline_SelectedFiberLaw _ _)
        intro M _
        exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl

/-- Every complete visible datum selected by the actual witness event pays the
private-decoding success constant. Good advice and a nonempty transferred
slice follow from positivity and are not additional hypotheses. -/
theorem visibleWitness_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (hvisible : VisibleTransfer.visibleWitness (law S k s d r β hβ hβ')
      AdviceLaw.completeObserve (slice S k s d r labeling α)
      (targetHit S k s d r labeling α) (α / 4) data = true) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      ActualConditionalLaw.datumAgreement S labeling (goodPredicate S labeling α hα hsmall) data := by
  obtain ⟨positive, hagree⟩ := VisibleTransfer.visibleWitness_conditional
    (law S k s d r β hβ hβ') AdviceLaw.completeObserve
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (α / 4) data hvisible
  obtain ⟨Nstar, hstar⟩ := exists_selected_private S labeling α β hβ hβ' data positive
  have hgood := good_of_selected_private S labeling α data Nstar hstar
  rw [conditional_eq_transferred S labeling α hα hsmall β hβ hβ' data hgood Nstar hstar positive] at hagree
  apply SelectedDecoding.observedAgreement_lower S labeling α hα hsmall
    (AdviceLaw.completeDraw data 0) hgood (datumMatrix S data Nstar) ?_ hagree
  exact (datumMatrix_rows S data Nstar).trans (datumMatrix_rows S data 0).symm

end MaxCutGames.Decoder.SelectedFiberLaw
end

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace MaxCutGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

variable {k s d r : ℕ}

def slopeVariation (k s d : ℕ) (β : ℝ) : ℝ :=
  Foundations.Information.totalVariation
    (SparseLaw.independentWeights
      (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
    (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d))

/-- The actual complete-data event has positive mass depending only on the
fixed inverse and alphabet parameters. -/
theorem visible_mass (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.visibleMass α g₀ s r ≤
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward AdviceLaw.completeObserve).probability
        (VisibleTransfer.visibleWitness (ActualSeedEvents.law S k s d r β hβ hβ')
          AdviceLaw.completeObserve (ActualSeedEvents.slice S k s d r labeling α)
          (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4)) := by
  have htv := (ActualSeedVariation.actual_totalVariation_le_slope S k s d r β hβ hβ').trans hvariation
  have h := VisibleTransfer.projected_witness_mass
    (ActualEvents.unrestricted S k s d r) (ActualSeedEvents.law S k s d r β hβ hβ')
    (ActualSeedEvents.pad S k s d r) AdviceLaw.completeObserve
    (ActualEvents.sliceEvent S k s d r labeling α) (ActualEvents.targetHit S k s d r labeling α)
    α g₀ (1 / (2 : ℝ) ^ (s * r)) hα.le
    (ActualEvents.slice_probability_lower S k s d r labeling α g₀ hgood)
    (ActualEvents.target_probability_lower S k s d r labeling α)
    (ConstantSelection.variationBudget_suffices hα s r htv)
  have hc : α * g₀ * (1 / (2 : ℝ) ^ (s * r)) / 8 =
      ConstantSelection.visibleMass α g₀ s r := by
    unfold ConstantSelection.visibleMass
    ring
  rw [hc] at h
  exact h

/-- Integrating a pointwise lower bound over a genuine probability event. -/
theorem event_expectation_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (f : Ω → ℝ)
    (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂) (hf : ∀ x, 0 ≤ f x)
    (hmass : γ₁ ≤ μ.probability event)
    (hpoint : ∀ x, event x = true → γ₂ ≤ f x) :
    γ₁ * γ₂ ≤ μ.expectation f := by
  have hweighted : μ.probability event * γ₂ ≤ μ.expectation f := by
    unfold FiniteDistribution.probability FiniteDistribution.expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : event x = true
    · simp only [hx, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hpoint x hx) (μ.nonnegative x)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact mul_nonneg (μ.nonnegative x) (hf x)
  exact (mul_le_mul_of_nonneg_right hmass hγ₂).trans hweighted

/-- End-to-end lower bound for actual local stochastic responses. No hidden
matrix, selected witness, or opposing observation is passed to a prover. -/
theorem actual_success_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.decodingMass α g₀ s r ≤
      (ActualSeedEvents.law S k s d r β hβ hβ').expectation
        (fun seed => VisiblePolicies.observedAgreement S labeling
          (SelectedPolicies.goodPredicate S labeling α hα hsmall)
          (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) := by
  let μ := ActualSeedEvents.law S k s d r β hβ hβ'
  let good := SelectedPolicies.goodPredicate S labeling α hα hsmall
  have h := event_expectation_lower (μ.pushforward AdviceLaw.completeObserve)
    (VisibleTransfer.visibleWitness μ AdviceLaw.completeObserve
      (ActualSeedEvents.slice S k s d r labeling α)
      (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4))
    (ActualConditionalLaw.datumAgreement S labeling good)
    (ConstantSelection.visibleMass α g₀ s r) (ConstantSelection.conditionalMass α s r)
    (ConstantSelection.conditionalMass_pos hα s r).le
    (ActualConditionalLaw.datumAgreement_nonneg S labeling good)
    (visible_mass S labeling α g₀ β hα hβ hβ' hgood hvariation)
    (SelectedFiberLaw.visibleWitness_decoding S labeling α hα hsmall β hβ hβ')
  rw [FiniteDistribution.expectation_pushforward] at h
  unfold ConstantSelection.decodingMass
  convert h using 1
  apply FiniteDistribution.expectation_congr
  intro seed
  exact ActualConditionalLaw.observedAgreement_seed S labeling good seed

end
end MaxCutGames.Decoder.ActualProjectedTransfer

end OAI
