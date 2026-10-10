import OAI.Analysis.KadisonKastler.RegularCoreOperators

namespace OAI

/-! # Bounds and adjoints for assembled measurable unitaries

The assembly is the actual multiplication operator on `L²(X,H)`.
An almost-everywhere fiber bound gives the same operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularUnitaryField_star_apply_ae (μ : Measure X)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    (star (regularUnitaryField μ U hU hUs) : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (star (U t) : H →L[ℂ] H) (f t) := by
  let u := regularUnitaryField μ U hU hUs
  let b := regularUnitaryFieldApply μ (fun t => star (U t)) hUs f
  have hb : (u : Lp H 2 μ →L[ℂ] Lp H 2 μ) b = f := by
    apply Lp.ext
    filter_upwards [regularUnitaryField_apply_ae μ U hU hUs b,
      regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f] with t hu hv
    rw [hu, hv]
    exact congrArg (fun T : H →L[ℂ] H => T (f t)) (U t).property.2
  have heq : (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f = b := by
    calc
      _ = (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((u : Lp H 2 μ →L[ℂ] Lp H 2 μ) b) :=
        congrArg (fun g => (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) g) hb.symm
      _ = b := congrArg (fun T : Lp H 2 μ →L[ℂ] Lp H 2 μ => T b) u.property.1
  rw [show (star (regularUnitaryField μ U hU hUs) : Lp H 2 μ →L[ℂ] Lp H 2 μ) f = b from heq]
  exact regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f

theorem norm_regularUnitaryField_sub_one_le (μ : Measure X)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ᵐ t ∂μ, ‖(U t : H →L[ℂ] H) - 1‖ ≤ a) :
    ‖(regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) - 1‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  change ∀ᵐ t ∂μ, ‖((regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f - f) t‖ ≤ a * ‖f t‖
  filter_upwards [hbound, regularUnitaryField_apply_ae μ U hU hUs f,
    Lp.coeFn_sub ((regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f) f]
    with t hb hu hs
  simp only [Pi.sub_apply] at hs
  rw [hs, hu]
  change ‖((U t : H →L[ℂ] H) - 1) (f t)‖ ≤ a * ‖f t‖
  exact (((U t : H →L[ℂ] H) - 1).le_opNorm (f t)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

end

end KadisonKastler

end OAI
