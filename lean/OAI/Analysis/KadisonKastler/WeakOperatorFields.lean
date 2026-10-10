import OAI.Analysis.KadisonKastler.BoundaryErgodicReduction
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar
import Mathlib.Topology.ContinuousMap.Bounded.Star

namespace OAI

/-! # Essentially bounded weak operator fields

The representatives are bounded operator-valued functions with measurable
evaluations of the function and its adjoint. Their closed C-star algebra
is quotiented by the closed star ideal of almost-everywhere zero fields.
The resulting norm is bounded by every essential operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The discrete topology is used only to package arbitrary bounded
families; all measurable assertions use the original measure space. -/
abbrev RawOperatorField (D H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  WithDiscreteTopology D →ᵇ (H →L[ℂ] H)

instance rawOperatorFieldCStar : CStarAlgebra (RawOperatorField D H) where

def rawOperatorEval (F : RawOperatorField D H) (x : D) : H →L[ℂ] H :=
  F (WithTopology.toTopology ⊥ x)

@[simp]
theorem rawOperatorEval_zero (x : D) : rawOperatorEval (0 : RawOperatorField D H) x = 0 := rfl

@[simp]
theorem rawOperatorEval_one (x : D) : rawOperatorEval (1 : RawOperatorField D H) x = 1 := rfl

@[simp]
theorem rawOperatorEval_add (F G : RawOperatorField D H) (x : D) :
    rawOperatorEval (F + G) x = rawOperatorEval F x + rawOperatorEval G x := rfl

@[simp]
theorem rawOperatorEval_mul (F G : RawOperatorField D H) (x : D) :
    rawOperatorEval (F * G) x = rawOperatorEval F x * rawOperatorEval G x := rfl

@[simp]
theorem rawOperatorEval_smul (c : ℂ) (F : RawOperatorField D H) (x : D) :
    rawOperatorEval (c • F) x = c • rawOperatorEval F x := rfl

@[simp]
theorem rawOperatorEval_star (F : RawOperatorField D H) (x : D) :
    rawOperatorEval (star F) x = star (rawOperatorEval F x) := rfl

theorem rawOperatorEval_continuous (x : D) :
    Continuous (fun F : RawOperatorField D H => rawOperatorEval F x) :=
  (BoundedContinuousFunction.evalCLM ℂ (WithTopology.toTopology ⊥ x)).continuous

def rawOperatorVectorEval (x : D) (ξ : H) : RawOperatorField D H →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp
    (BoundedContinuousFunction.evalCLM ℂ (WithTopology.toTopology ⊥ x))

@[simp]
theorem rawOperatorVectorEval_apply (x : D) (ξ : H) (F : RawOperatorField D H) :
    rawOperatorVectorEval x ξ F = rawOperatorEval F x ξ := rfl

variable [MeasurableSpace D] (μ : Measure D)

def IsMeasurableOperatorField (F : RawOperatorField D H) : Prop :=
  ∀ ξ : H,
    AEStronglyMeasurable (fun x => rawOperatorEval F x ξ) μ ∧
    AEStronglyMeasurable (fun x => star (rawOperatorEval F x) ξ) μ

/-- Measurable operator fields form a star subalgebra. -/
def measurableOperatorSubalgebra : StarSubalgebra ℂ (RawOperatorField D H) where
  carrier := IsMeasurableOperatorField μ
  zero_mem' := by
    intro ξ
    constructor <;> simpa using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => (0 : H)) μ)
  one_mem' := by
    intro ξ
    constructor <;> simpa using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => ξ) μ)
  add_mem' {F G} hF hG := by
    intro ξ
    constructor
    · convert (hF ξ).1.add (hG ξ).1 using 1
      funext x
      simp only [rawOperatorEval_add, add_apply, Pi.add_apply]
    · convert (hF ξ).2.add (hG ξ).2 using 1
      funext x
      simp only [rawOperatorEval_add, star_add, add_apply, Pi.add_apply]
  mul_mem' {F G} hF hG := by
    intro ξ
    constructor
    · exact aestronglyMeasurable_field_apply (rawOperatorEval F) (fun η => (hF η).1)
        (fun x => rawOperatorEval G x ξ) (hG ξ).1
    · simpa only [rawOperatorEval_mul, star_mul, mul_apply_eq_comp] using
        aestronglyMeasurable_field_apply (fun x => star (rawOperatorEval G x))
          (fun η => (hG η).2) (fun x => star (rawOperatorEval F x) ξ) (hF ξ).2
  algebraMap_mem' c := by
    intro ξ
    constructor
    · change AEStronglyMeasurable (fun _ : D => (algebraMap ℂ (H →L[ℂ] H) c) ξ) μ
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun _ : D => star (algebraMap ℂ (H →L[ℂ] H) c) ξ) μ
      exact aestronglyMeasurable_const
  star_mem' {F} hF := by
    intro ξ
    simpa only [rawOperatorEval_star, star_star] using And.intro (hF ξ).2 (hF ξ).1

/-- The measurability condition is preserved by operator-norm limits. -/
instance measurableOperatorSubalgebra_closed :
    IsClosed (measurableOperatorSubalgebra (H := H) μ : Set (RawOperatorField D H)) := by
  apply IsSeqClosed.isClosed
  intro F G hF hG ξ
  constructor
  · exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n ξ).1)
      (Eventually.of_forall fun x =>
        ((rawOperatorVectorEval x ξ).continuous.tendsto G).comp hG)
  · exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n ξ).2)
      (Eventually.of_forall fun x =>
        ((rawOperatorVectorEval x ξ).continuous.tendsto (star G)).comp
          ((continuous_star.tendsto G).comp hG))

abbrev WeakOperatorRepresentative : Type _ := measurableOperatorSubalgebra (H := H) μ

instance weakOperatorRepresentativeCStar :
    CStarAlgebra (WeakOperatorRepresentative (H := H) μ) := inferInstance

namespace WeakOperatorRepresentative

variable {μ}

def eval (F : WeakOperatorRepresentative (H := H) μ) (x : D) : H →L[ℂ] H :=
  rawOperatorEval F.val x

@[simp]
theorem eval_zero (x : D) : eval (0 : WeakOperatorRepresentative (H := H) μ) x = 0 := rfl

@[simp]
theorem eval_one (x : D) : eval (1 : WeakOperatorRepresentative (H := H) μ) x = 1 := rfl

@[simp]
theorem eval_add (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F + G) x = eval F x + eval G x := rfl

@[simp]
theorem eval_mul (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F * G) x = eval F x * eval G x := rfl

@[simp]
theorem eval_sub (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F - G) x = eval F x - eval G x := rfl

@[simp]
theorem eval_neg (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (-F) x = -eval F x := rfl

@[simp]
theorem eval_smul (c : ℂ) (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (c • F) x = c • eval F x := rfl

@[simp]
theorem eval_star (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (star F) x = star (eval F x) := rfl

theorem eval_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => eval F x ξ) μ := (F.property ξ).1

theorem star_eval_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => star (eval F x) ξ) μ := (F.property ξ).2

theorem eval_norm_le (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    ‖eval F x‖ ≤ ‖F‖ := F.val.norm_coe_le_norm _

theorem eval_continuous (x : D) :
    Continuous (fun F : WeakOperatorRepresentative (H := H) μ => eval F x) :=
  (rawOperatorEval_continuous x).comp continuous_subtype_val

/-- Bundle any uniformly bounded measurable operator field. -/
def mk (f : D → H →L[ℂ] H) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x : WithDiscreteTopology D => f x.ofTopology) C (fun x => hC x.ofTopology),
    fun ξ => ⟨hf ξ, hfstar ξ⟩⟩

@[simp]
theorem eval_mk (f : D → H →L[ℂ] H) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) (x : D) :
    eval (mk f C hC hf hfstar) x = f x := rfl

theorem norm_mk_le (f : D → H →L[ℂ] H) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) :
    ‖mk f C hC hf hfstar‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC0).mpr (fun x => hC x.ofTopology)

end WeakOperatorRepresentative

/-- Constant operators as measurable fields. -/
def operatorRepresentativeConst : (H →L[ℂ] H) →⋆ₐ[ℂ] WeakOperatorRepresentative (H := H) μ where
  toFun T := ⟨BoundedContinuousFunction.const _ T, by
    intro ξ
    constructor
    · change AEStronglyMeasurable (fun _ : D => T ξ) μ
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun _ : D => star T ξ) μ
      exact aestronglyMeasurable_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem operatorRepresentativeConst_eval (T : H →L[ℂ] H) (x : D) :
    WeakOperatorRepresentative.eval (operatorRepresentativeConst μ T) x = T := rfl

/-- Equality almost everywhere is an algebra congruence. -/
def operatorFieldAERel : RingCon (WeakOperatorRepresentative (H := H) μ) where
  r F G := WeakOperatorRepresentative.eval F =ᵐ[μ] WeakOperatorRepresentative.eval G
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl, fun h => h.symm, fun h k => h.trans k⟩
  add' h k := h.add k
  mul' h k := h.mul k

/-- The zero fields form a closed two-sided star ideal. -/
def operatorFieldZeroIdeal :
    CuntzPureness.ClosedStarIdeal (WeakOperatorRepresentative (H := H) μ) where
  ideal := TwoSidedIdeal.ofRingCon (operatorFieldAERel μ)
  star_mem {F} hF := by
    change WeakOperatorRepresentative.eval (star F) =ᵐ[μ] fun _ => 0
    change WeakOperatorRepresentative.eval F =ᵐ[μ] fun _ => 0 at hF
    filter_upwards [hF] with x hx
    simp only [WeakOperatorRepresentative.eval_star, hx, star_zero]
  isClosed := by
    apply IsSeqClosed.isClosed
    intro F G hF hG
    change WeakOperatorRepresentative.eval G =ᵐ[μ] fun _ => 0
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, WeakOperatorRepresentative.eval (F n) x = 0 :=
      ae_all_iff.mpr hF
    filter_upwards [hall] with x hx
    have ht := ((WeakOperatorRepresentative.eval_continuous x).tendsto G).comp hG
    have hz : Tendsto (fun n : ℕ => WeakOperatorRepresentative.eval (F n) x) atTop (𝓝 0) := by
      simpa only [hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H →L[ℂ] H)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht hz

local instance weakOperatorRepresentativeOrder :
    PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance weakOperatorRepresentativeStarOrder :
    StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _

abbrev WeakOperatorField := (operatorFieldZeroIdeal (H := H) μ).Quotient

instance weakOperatorFieldCStar : CStarAlgebra (WeakOperatorField (H := H) μ) := inferInstance

def operatorFieldQuotient : WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ]
    WeakOperatorField (H := H) μ := (operatorFieldZeroIdeal μ).quotientStarHom

theorem operatorFieldQuotient_surjective : Function.Surjective (operatorFieldQuotient (H := H) μ) :=
  (operatorFieldZeroIdeal μ).quotientMap_surjective

theorem operatorFieldQuotient_eq_iff (F G : WeakOperatorRepresentative (H := H) μ) :
    operatorFieldQuotient μ F = operatorFieldQuotient μ G ↔
      WeakOperatorRepresentative.eval F =ᵐ[μ] WeakOperatorRepresentative.eval G := by
  change (operatorFieldAERel (H := H) μ).mk' F = (operatorFieldAERel (H := H) μ).mk' G ↔ _
  exact Quotient.eq

theorem operatorFieldQuotient_norm_le (F : WeakOperatorRepresentative (H := H) μ) :
    ‖operatorFieldQuotient μ F‖ ≤ ‖F‖ := (operatorFieldZeroIdeal μ).quotientMap_norm_le F

def operatorFieldConst : (H →L[ℂ] H) →⋆ₐ[ℂ] WeakOperatorField (H := H) μ :=
  (operatorFieldQuotient μ).comp (operatorRepresentativeConst μ)

/-- An essential operator-norm bound bounds the actual quotient norm.
The exceptional-set replacement is legitimate even when that set itself
has not been supplied as a measurable set. -/
theorem operatorFieldQuotient_norm_le_of_ae
    (F : WeakOperatorRepresentative (H := H) μ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤ C) :
    ‖operatorFieldQuotient μ F‖ ≤ C := by
  let f : D → H →L[ℂ] H := fun x =>
    if ‖WeakOperatorRepresentative.eval F x‖ ≤ C then WeakOperatorRepresentative.eval F x else 0
  have hnorm (x : D) : ‖f x‖ ≤ C := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · simpa only [norm_zero] using hC
  have heq : WeakOperatorRepresentative.eval F =ᵐ[μ] f :=
    hF.mono fun x hx => by simp [f, hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T => T ξ) hx)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T : H →L[ℂ] H => star T ξ) hx)
  let G := WeakOperatorRepresentative.mk f C hnorm hm hs
  have hFG : operatorFieldQuotient μ F = operatorFieldQuotient μ G :=
    (operatorFieldQuotient_eq_iff μ F G).mpr heq
  rw [hFG]
  exact (operatorFieldQuotient_norm_le μ G).trans
    (WeakOperatorRepresentative.norm_mk_le f hC hnorm hm hs)

end

end KadisonKastler

end OAI
