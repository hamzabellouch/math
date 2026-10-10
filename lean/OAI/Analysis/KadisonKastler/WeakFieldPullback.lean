import OAI.Analysis.KadisonKastler.WeakFieldCoefficients
import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # Nonsingular pullback of weak operator fields

Composition preserves the measurable representatives and their uniform
bound. Nonsingularity makes the construction independent of representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

theorem eq_of_eval {F G : WeakOperatorRepresentative (H := H) μ}
    (h : ∀ x, eval F x = eval G x) : F = G := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact h x.ofTopology

/-- Pullback of bounded measurable representatives by a nonsingular map. -/
def pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ) :
    WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ]
      WeakOperatorRepresentative (H := H) μ where
  toFun F := mk (fun x => eval F (T x)) ‖F‖ (fun x => eval_norm_le F (T x))
    (fun ξ => (eval_aestronglyMeasurable F ξ).comp_quasiMeasurePreserving hT)
    (fun ξ => (star_eval_aestronglyMeasurable F ξ).comp_quasiMeasurePreserving hT)
  map_one' := by apply eq_of_eval; intro x; rfl
  map_mul' F G := by apply eq_of_eval; intro x; rfl
  map_zero' := by apply eq_of_eval; intro x; rfl
  map_add' F G := by apply eq_of_eval; intro x; rfl
  commutes' c := by apply eq_of_eval; intro x; rfl
  map_star' F := by apply eq_of_eval; intro x; rfl

@[simp]
theorem eval_pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (pullback T hT F) x = eval F (T x) := rfl

theorem norm_pullback_le (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    ‖pullback T hT F‖ ≤ ‖F‖ :=
  norm_mk_le _ (norm_nonneg F) _ _ _

theorem pullback_congr_ae (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    {F G : WeakOperatorRepresentative (H := H) μ} (hFG : eval F =ᵐ[μ] eval G) :
    eval (pullback T hT F) =ᵐ[μ] eval (pullback T hT G) :=
  hT.ae hFG

@[simp]
theorem pullback_constant (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (A : H →L[ℂ] H) :
    pullback T hT (operatorRepresentativeConst μ A) = operatorRepresentativeConst μ A := by
  apply eq_of_eval
  intro x
  rfl

@[simp]
theorem pullback_id (F : WeakOperatorRepresentative (H := H) μ) :
    pullback id (Measure.QuasiMeasurePreserving.id μ) F = F := by
  apply eq_of_eval
  intro x
  rfl

theorem pullback_comp (T S : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullback S hS (pullback T hT F) = pullback (T ∘ S) (hT.comp hS) F := by
  apply eq_of_eval
  intro x
  rfl

end WeakOperatorRepresentative

namespace WeakOperatorField

private def pullbackValue (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (q : WeakOperatorField (H := H) μ) : WeakOperatorField (H := H) μ :=
  operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT (representative q))

private theorem pullbackValue_quotient (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullbackValue (H := H) T hT (operatorFieldQuotient (H := H) μ F) =
      operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT F) := by
  apply (operatorFieldQuotient_eq_iff μ _ _).mpr
  exact WeakOperatorRepresentative.pullback_congr_ae T hT
    ((operatorFieldQuotient_eq_iff μ _ _).mp (quotient_representative _))

private theorem pullbackValue_one (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) :
    pullbackValue (H := H) T hT 1 = 1 := by
    calc
      pullbackValue (H := H) T hT 1 = pullbackValue (H := H) T hT
          (operatorFieldQuotient (H := H) μ (1 : WeakOperatorRepresentative (H := H) μ)) :=
        congrArg (pullbackValue (H := H) T hT) (operatorFieldQuotient (H := H) μ).map_one.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT 1) :=
        pullbackValue_quotient T hT _
      _ = 1 := by rw [map_one, map_one]
private theorem pullbackValue_mul (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q r : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (q * r) = pullbackValue (H := H) T hT q * pullbackValue (H := H) T hT r := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    obtain ⟨G, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ r
    rw [← map_mul, pullbackValue_quotient, map_mul, map_mul,
      pullbackValue_quotient, pullbackValue_quotient]
private theorem pullbackValue_zero (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) :
    pullbackValue (H := H) T hT 0 = 0 := by
    calc
      pullbackValue (H := H) T hT 0 = pullbackValue (H := H) T hT
          (operatorFieldQuotient (H := H) μ (0 : WeakOperatorRepresentative (H := H) μ)) :=
        congrArg (pullbackValue (H := H) T hT) (operatorFieldQuotient (H := H) μ).map_zero.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT 0) :=
        pullbackValue_quotient T hT _
      _ = 0 := by rw [map_zero, map_zero]
private theorem pullbackValue_add (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q r : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (q + r) = pullbackValue (H := H) T hT q + pullbackValue (H := H) T hT r := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    obtain ⟨G, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ r
    rw [← map_add, pullbackValue_quotient, map_add, map_add,
      pullbackValue_quotient, pullbackValue_quotient]
private theorem pullbackValue_algebraMap (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (c : ℂ) :
    pullbackValue (H := H) T hT (algebraMap ℂ (WeakOperatorField (H := H) μ) c) =
      algebraMap ℂ (WeakOperatorField (H := H) μ) c := by
    let a : WeakOperatorRepresentative (H := H) μ :=
      algebraMap ℂ (WeakOperatorRepresentative (H := H) μ) c
    have hq : operatorFieldQuotient (H := H) μ a =
        algebraMap ℂ (WeakOperatorField (H := H) μ) c :=
      (operatorFieldQuotient (H := H) μ).commutes c
    calc
      pullbackValue (H := H) T hT (algebraMap ℂ (WeakOperatorField (H := H) μ) c) =
          pullbackValue (H := H) T hT (operatorFieldQuotient (H := H) μ a) :=
        congrArg (pullbackValue (H := H) T hT) hq.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT a) :=
        pullbackValue_quotient T hT a
      _ = operatorFieldQuotient (H := H) μ a := congrArg (operatorFieldQuotient (H := H) μ)
        ((WeakOperatorRepresentative.pullback (H := H) T hT).commutes c)
      _ = algebraMap ℂ (WeakOperatorField (H := H) μ) c := hq
private theorem pullbackValue_star (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (star q) = star (pullbackValue (H := H) T hT q) := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    rw [← map_star, pullbackValue_quotient, map_star, map_star, pullbackValue_quotient]

/-- Nonsingular pullback is a unital star-algebra homomorphism of the
actual almost-everywhere quotient. -/
def pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ) :
    WeakOperatorField (H := H) μ →⋆ₐ[ℂ] WeakOperatorField (H := H) μ where
  toFun := pullbackValue (H := H) T hT
  map_one' := pullbackValue_one T hT
  map_mul' := pullbackValue_mul T hT
  map_zero' := pullbackValue_zero T hT
  map_add' := pullbackValue_add T hT
  commutes' := pullbackValue_algebraMap T hT
  map_star' := pullbackValue_star T hT

theorem pullback_quotient (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullback T hT (operatorFieldQuotient (H := H) μ F) =
      operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT F) :=
  pullbackValue_quotient T hT F

theorem norm_pullback_le (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (q : WeakOperatorField (H := H) μ) : ‖pullback T hT q‖ ≤ ‖q‖ :=
  (operatorFieldQuotient_norm_le μ _).trans
    ((WeakOperatorRepresentative.norm_pullback_le T hT _).trans (norm_representative_le q))

@[simp]
theorem pullback_constant (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (A : H →L[ℂ] H) : pullback T hT (operatorFieldConst μ A) = operatorFieldConst μ A := by
  change pullback T hT (operatorFieldQuotient (H := H) μ (operatorRepresentativeConst μ A)) = _
  rw [pullback_quotient, WeakOperatorRepresentative.pullback_constant]
  rfl

@[simp]
theorem pullback_id (q : WeakOperatorField (H := H) μ) :
    pullback id (Measure.QuasiMeasurePreserving.id μ) q = q := by
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
  rw [pullback_quotient, WeakOperatorRepresentative.pullback_id]

theorem pullback_comp (T S : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hS : Measure.QuasiMeasurePreserving S μ μ) (q : WeakOperatorField (H := H) μ) :
    pullback S hS (pullback T hT q) = pullback (T ∘ S) (hT.comp hS) q := by
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
  rw [pullback_quotient, pullback_quotient, pullback_quotient,
    WeakOperatorRepresentative.pullback_comp]

variable [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- Pulling back an operator field pulls back every scalar coefficient. -/
theorem coefficient_pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (q : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (pullback T hT q) ξ η =
      scalarInfinityPullback T hT (coefficient q ξ η) := by
  rw [← quotient_representative q, pullback_quotient, coefficient_quotient,
    coefficient_quotient]
  apply Lp.ext
  filter_upwards [WeakOperatorRepresentative.coefficient_ae
      (WeakOperatorRepresentative.pullback (H := H) T hT (representative q)) ξ η,
    scalarInfinityPullback_ae T hT
      (WeakOperatorRepresentative.coefficient (representative q) ξ η),
    hT.ae (WeakOperatorRepresentative.coefficient_ae (representative q) ξ η)]
      with x hleft hright hcoefficient
  rw [hleft, hright, hcoefficient, WeakOperatorRepresentative.eval_pullback]

end WeakOperatorField

end

end KadisonKastler

end OAI
