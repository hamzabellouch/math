import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

/-! A fixed principal branch is globally bounded, is smooth away from
its cut, and has precisely the intrinsic circle differential there.
Thus a local branch consumes only the original coordinate's energy. -/

open Set Filter Function MeasureTheory
open scoped Topology ENNReal ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem circleBranch_mem_Ico {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) :
    circleBranch f a x ∈ Ico a (a + 1) := (AddCircle.equivIco 1 a (f x)).property

theorem circleBranch_abs_le {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) :
    |circleBranch f a x| ≤ |a| + 1 := by
  have h := circleBranch_mem_Ico f a x
  have ha := neg_abs_le a
  have ha' := le_abs_self a
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem continuousOn_circleBranch {X : Type*} [TopologicalSpace X]
    {f : X → UnitAddCircle} {U : Set X} (hf : ContinuousOn f U) (a : ℝ)
    (hcut : ∀ x ∈ U, f x ≠ (a : UnitAddCircle)) :
    ContinuousOn (circleBranch f a) U := by
  intro x hx
  exact continuous_subtype_val.continuousAt.comp_continuousWithinAt
    ((AddCircle.continuousAt_equivIco 1 a (hcut x hx)).comp_continuousWithinAt (hf x hx))

theorem smooth_circleBranch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) {A : Set E} (hA : A ⊆ U)
    (hcut : ∀ x ∈ A, f x ≠ (a : UnitAddCircle)) :
    ContDiffOn ℝ ∞ (circleBranch f a) A :=
  fun x hx => (hf x (hA hx) a (hcut x hx)).contDiffWithinAt

theorem fderiv_circleBranch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) {x : E} (hx : x ∈ U) (hcut : f x ≠ (a : UnitAddCircle)) :
    fderiv ℝ (circleBranch f a) x = circleFDeriv f x := by
  have hb := (hf x hx a hcut).continuousAt
  have hc : ContinuousAt f x := by
    have hp := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hb
    change ContinuousAt (fun y => (circleBranch f a y : UnitAddCircle)) x at hp
    exact hp.congr (Eventually.of_forall (coe_circleBranch f a))
  exact (circleFDeriv_eq_lift hc hb (Eventually.of_forall (coe_circleBranch f a))).symm

theorem circleBranch_energy_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {f : E → UnitAddCircle} {U A : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) (hAm : MeasurableSet A) (hA : A ⊆ U)
    (hcut : ∀ x ∈ A, f x ≠ (a : UnitAddCircle))
    (μ : Measure E) :
    (∫⁻ x in A, ENNReal.ofReal ‖fderiv ℝ (circleBranch f a) x‖ ^ 2 ∂μ) ≤
      ∫⁻ x in U, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
  calc
    _ = ∫⁻ x in A, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
      apply setLIntegral_congr_fun hAm
      intro x hx
      dsimp only
      rw [fderiv_circleBranch hf a (hA hx) (hcut x hx)]
    _ ≤ _ := lintegral_mono_set hA

end CircleDomainRigidity.FiniteTransfer

end

end OAI
