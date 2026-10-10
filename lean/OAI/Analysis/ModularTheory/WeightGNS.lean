import OAI.Analysis.ModularTheory.WeightGram

namespace OAI

/-! The concrete Hilbert-space vector of a finite-square-weight core operator.
It is the limit of the actual cutoff vectors. The left-action identity is
proved from continuity, without assuming the weight is tracial. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

variable (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
  (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
  (hfin : modularCoreSquareWeight S T < ⊤)

def modularWeightVector : Lp H 2 (volume : Measure ℝ) :=
  (exists_modularCoreWeightVector_limit S T hT hfin).choose

lemma modularWeightVector_tendsto :
    Tendsto (fun n => T (modularCoreWeightVector S n)) atTop
      (𝓝 (modularWeightVector S T hT hfin)) :=
  (exists_modularCoreWeightVector_limit S T hT hfin).choose_spec

lemma modularWeightVector_norm_sq :
    ‖modularWeightVector S T hT hfin‖ ^ 2 = (modularCoreSquareWeight S T).toReal := by
  apply tendsto_nhds_unique
    (((modularWeightVector_tendsto S T hT hfin).norm).pow 2)
  exact modularCoreWeightVector_norm_sq_tendsto S T hT hfin

lemma modularWeightVector_eq_zero_iff :
    modularWeightVector S T hT hfin = 0 ↔ T = 0 := by
  constructor
  · intro hz
    have hw := modularWeightVector_norm_sq S T hT hfin
    rw [hz, norm_zero, zero_pow (by decide)] at hw
    have hzero : modularCoreSquareWeight S T = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hw.symm).resolve_right hfin.ne
    exact (modularCoreSquareWeight_eq_zero_iff S T hT).mp hzero
  · intro hz
    apply tendsto_nhds_unique (modularWeightVector_tendsto S T hT hfin)
    simpa only [hz, zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp H 2 (volume : Measure ℝ)))
        atTop (𝓝 0))

include hfin in
lemma modularCoreSquareWeight_mul_finite
    (R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularCoreSquareWeight S (R * T) < ⊤ :=
  (modularCoreSquareWeight_mul_le S R T).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

lemma modularWeightVector_mul
    (R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hR : R ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    modularWeightVector S (R * T) (mul_mem hR hT)
        (modularCoreSquareWeight_mul_finite S T hfin R) =
      R (modularWeightVector S T hT hfin) := by
  apply tendsto_nhds_unique (modularWeightVector_tendsto S (R * T) _ _)
  exact R.continuous.continuousAt.tendsto.comp (modularWeightVector_tendsto S T hT hfin)

include hfin in
lemma modularCoreSquareWeight_add_finite
    (R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hRfin : modularCoreSquareWeight S R < ⊤) :
    modularCoreSquareWeight S (R + T) < ⊤ :=
  (modularCoreSquareWeight_add_le S R T).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hRfin, hfin⟩))

lemma modularWeightVector_add
    (R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hR : R ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hRfin : modularCoreSquareWeight S R < ⊤) :
    modularWeightVector S (R + T) (add_mem hR hT)
        (modularCoreSquareWeight_add_finite S T hfin R hRfin) =
      modularWeightVector S R hR hRfin + modularWeightVector S T hT hfin := by
  apply tendsto_nhds_unique (modularWeightVector_tendsto S (R + T) _ _)
  exact (modularWeightVector_tendsto S R hR hRfin).add
    (modularWeightVector_tendsto S T hT hfin)

end WeakPureInfiniteness

end

end OAI
