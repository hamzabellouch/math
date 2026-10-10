import OAI.Analysis.KadisonKastler.BoundaryErgodicReduction
import OAI.Analysis.KadisonKastler.FaithfulRepresentation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Operators on the actual regular Hilbert space

The regular core acts on `L²(ℝ,H)`, with a constant operator
representation and multiplication by a measurable unitary
field. The latter gives the gauge transformation used to write the core
embedding as a faithful conjugate of the constant representation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {D H : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pointwise action of a constant bounded operator on a Hilbert-valued
`L²` space. -/
def regularConstantOperator (μ : Measure D) (T : H →L[ℂ] H) :
    Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  T.compLpL 2 μ

omit [CompleteSpace H] in
theorem regularConstantOperator_apply_ae (μ : Measure D) (T : H →L[ℂ] H)
    (f : Lp H 2 μ) :
    regularConstantOperator μ T f =ᵐ[μ] fun t => T (f t) :=
  T.coeFn_compLpL f

omit [CompleteSpace H] in
theorem regularConstantOperator_mul (μ : Measure D) (T S : H →L[ℂ] H) :
    regularConstantOperator μ (T * S) =
      regularConstantOperator μ T * regularConstantOperator μ S := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantOperator_apply_ae μ (T * S) f,
    regularConstantOperator_apply_ae μ T (regularConstantOperator μ S f),
    regularConstantOperator_apply_ae μ S f] with t hTS hT hS
  simp only [mul_apply_eq_comp]
  rw [hTS, hT, hS]
  rfl

omit [CompleteSpace H] in
theorem regularConstantOperator_one (μ : Measure D) :
    regularConstantOperator μ (1 : H →L[ℂ] H) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantOperator_apply_ae μ (1 : H →L[ℂ] H) f] with t ht
  simpa only [one_apply_eq_self] using ht

theorem regularConstantOperator_star (μ : Measure D) (T : H →L[ℂ] H) :
    regularConstantOperator μ (star T) = star (regularConstantOperator μ T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularConstantOperator_apply_ae μ (star T) f,
    regularConstantOperator_apply_ae μ T g] with t hf hg
  simp only [ContinuousLinearMap.star_eq_adjoint] at hf
  rw [hf, hg, ContinuousLinearMap.adjoint_inner_right]

/-- The constant copy of `B(H)` on a Hilbert-valued `L²` space. -/
def regularConstantHom (μ : Measure D) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := regularConstantOperator μ
  map_one' := regularConstantOperator_one μ
  map_mul' := regularConstantOperator_mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [regularConstantOperator_apply_ae μ (0 : H →L[ℂ] H) f,
      Lp.coeFn_zero H 2 μ] with t ht hz
    simpa only [zero_apply] using ht.trans hz.symm
  map_add' T S := ContinuousLinearMap.add_compLpL T S
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [regularConstantOperator_apply_ae μ (algebraMap ℂ (H →L[ℂ] H) c) f,
      Lp.coeFn_smul c f] with t ht hc
    simpa only [Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self] using ht.trans hc.symm
  map_star' := regularConstantOperator_star μ

theorem regularConstantHom_apply_ae (μ : Measure D) (T : H →L[ℂ] H)
    (f : Lp H 2 μ) :
    regularConstantHom μ T f =ᵐ[μ] fun t => T (f t) :=
  regularConstantOperator_apply_ae μ T f

/-- A finite positive-measure test set makes the constant representation
faithful, without requiring a finite total measure. -/
theorem regularConstantHom_injective (μ : Measure D) (s : Set D)
    (hs : MeasurableSet s) (hfin : μ s ≠ ∞) (hpos : μ s ≠ 0) :
    Function.Injective (regularConstantHom (H := H) μ) := by
  intro T S hTS
  apply ContinuousLinearMap.ext
  intro x
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfin x
  have heq : regularConstantHom μ T f = regularConstantHom μ S f :=
    congrArg (fun R : Lp H 2 μ →L[ℂ] Lp H 2 μ => R f) hTS
  have hpoint : ∀ᵐ t ∂μ, t ∈ s → T x = S x := by
    filter_upwards [regularConstantHom_apply_ae μ T f,
      regularConstantHom_apply_ae μ S f,
      (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfin) (c := x))]
      with t hT hS hf
    intro ht
    rw [hf ht] at hT hS
    exact hT.symm.trans ((congrArg (fun v : Lp H 2 μ => v t) heq).trans hS)
  obtain ⟨t, ht, h⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hpoint)
  exact h ht

/-- Multiplication of `L²` vectors by a measurable unitary field. -/
def regularUnitaryFieldApply (μ : Measure D) (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) : Lp H 2 μ :=
  ((Lp.memLp f).congr_norm
    (aestronglyMeasurable_field_apply (fun t => (U t : H →L[ℂ] H)) hU f
      (Lp.aestronglyMeasurable f))
    (Eventually.of_forall (fun t => (Unitary.norm_map (U t) (f t)).symm))).toLp _

theorem regularUnitaryFieldApply_ae (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    regularUnitaryFieldApply μ U hU f =ᵐ[μ] fun t => (U t : H →L[ℂ] H) (f t) :=
  MemLp.coeFn_toLp _

theorem norm_regularUnitaryFieldApply (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) : ‖regularUnitaryFieldApply μ U hU f‖ = ‖f‖ := by
  have he : ∀ᵐ t ∂μ, ‖regularUnitaryFieldApply μ U hU f t‖ = ‖f t‖ :=
    (regularUnitaryFieldApply_ae μ U hU f).mono
      (fun t ht => by rw [ht, Unitary.norm_map])
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

/-- The gauge operator as a genuine unitary on the regular Hilbert space. -/
def regularUnitaryField (μ : Measure D) (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ) :
    unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  Unitary.linearIsometryEquiv.symm
    { toFun := regularUnitaryFieldApply μ U hU
      invFun := regularUnitaryFieldApply μ (fun t => star (U t)) hUs
      map_add' f g := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU (f + g),
          regularUnitaryFieldApply_ae μ U hU f,
          regularUnitaryFieldApply_ae μ U hU g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (regularUnitaryFieldApply μ U hU f)
            (regularUnitaryFieldApply μ U hU g)] with t hfg hf hg ha hb
        rw [hfg, ha, hb]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU (c • f),
          regularUnitaryFieldApply_ae μ U hU f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (regularUnitaryFieldApply μ U hU f)] with t hc hf ha hb
        rw [hc, ha, hb]
        simp only [Pi.smul_apply]
        rw [hf, map_smul]
      norm_map' := norm_regularUnitaryFieldApply μ U hU
      left_inv f := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs
            (regularUnitaryFieldApply μ U hU f), regularUnitaryFieldApply_ae μ U hU f]
          with t hs hf
        rw [hs, hf]
        exact congrArg (fun R : H →L[ℂ] H => R (f t))
          (Unitary.star_mul_self_of_mem (U t).property)
      right_inv f := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU
            (regularUnitaryFieldApply μ (fun t => star (U t)) hUs f),
          regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f]
          with t hU hUs
        rw [hU, hUs]
        exact congrArg (fun R : H →L[ℂ] H => R (f t))
          (Unitary.mul_star_self_of_mem (U t).property) }

theorem regularUnitaryField_apply_ae (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    (regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (U t : H →L[ℂ] H) (f t) :=
  regularUnitaryFieldApply_ae μ U hU f

/-- The actual real-line regular Hilbert space. -/
abbrev RegularCoreHilbert (H : Type*) [NormedAddCommGroup H] :=
  Lp H 2 (volume : Measure ℝ)

theorem real_regularConstantHom_injective :
    Function.Injective (regularConstantHom (H := H) (volume : Measure ℝ)) := by
  apply regularConstantHom_injective volume (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
  · simp only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, ENNReal.one_ne_top,
      not_false_eq_true]
  · simp only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, one_ne_zero,
      not_false_eq_true]

theorem real_regularConstantHom_completelyIsometric :
    CompletelyIsometric (regularConstantHom (H := H) (volume : Measure ℝ)).toAlgHom.toLinearMap :=
  injective_starAlgHom_completelyIsometric _ real_regularConstantHom_injective

end

end KadisonKastler

end OAI
