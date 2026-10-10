import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CylinderMeasure

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def ContinuousTails (f : ScalarField 2) : Prop :=
  ∃ F : ℝ → compatible 2, ContinuousOn F (Ici 0) ∧
    ∀ t X, (F t).val.1 X = f t X

def C1Tails (f : ScalarField 2) : Prop :=
  ∃ F dF : ℝ → compatible 2,
    ContinuousOn F (Ici 0) ∧ ContinuousOn dF (Ici 0) ∧
    (∀ t X, (F t).val.1 X = f t X) ∧
    (∀ t ≥ 0, HasDerivWithinAt F (dF t) (Ici 0) t)

def evalLinear (X : Coord 2) : compatible 2 →ₗ[ℝ] ℝ where
  toFun f := f.val.1 X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def eval (X : Coord 2) : compatible 2 →L[ℝ] ℝ where
  toLinearMap := evalLinear X
  cont := AddMonoidHomClass.continuous_of_bound (evalLinear X) 1 (fun f => by
    change ‖f.val.1 X‖ ≤ 1 * ‖f.val‖
    rw [one_mul]
    exact (BoundedContinuousFunction.norm_coe_le_norm f.val.1.toBCF X).trans (norm_fst_le f.val))

@[simp] theorem eval_apply (X : Coord 2) (f : compatible 2) : eval X f = f.val.1 X := rfl

theorem ContinuousTails.integrable {f : ScalarField 2} (hf : ContinuousTails f) (t : ℝ) :
    Integrable (f t) := by
  obtain ⟨F, -, hr⟩ := hf
  have H : (fun X => (F t).val.2 X) =ᵐ[volume] (f t) := by
    have ht : (fun X => (F t).val.2 X) =ᵐ[volume] (fun X => (F t).val.1 X) := (F t).property
    simpa only [hr] using ht
  exact (L1.integrable_coeFn (F t).val.2).congr H

theorem ContinuousTails.memLp {f : ScalarField 2} (hf : ContinuousTails f) (t : ℝ) :
    MemLp (f t) 2 volume := by
  obtain ⟨F, -, hr⟩ := hf
  simpa only [hr] using member_memLp (F t)

theorem ContinuousTails.cylinderL2 {f : ScalarField 2} (hf : ContinuousTails f) (T : ℝ) :
    Cylinder.continuousL2On (fun t x => f t x.1) T := by
  obtain ⟨F, hF, hr⟩ := hf
  refine ⟨fun t => Cylinder.tailsToL2 (F t),
    Cylinder.tailsToL2.continuous.comp_continuousOn (hF.mono Icc_subset_Ici_self), ?_⟩
  intro t _
  simpa only [hr] using Cylinder.coeFn_tailsToL2 (F t)

theorem ContinuousTails.bounded {f : ScalarField 2} (hf : ContinuousTails f)
    {T : ℝ} (hT : 0 ≤ T) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ∀ X, |f t X| ≤ B := by
  obtain ⟨F, hF, hr⟩ := hf
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (f := fun t => ‖F t‖) (nonempty_Icc.mpr hT)
    (ContinuousOn.norm (E := compatible 2) (hF.mono Icc_subset_Ici_self))
  refine ⟨‖F s‖, norm_nonneg (F s), fun t ht X => ?_⟩
  calc
    |f t X| = ‖(F t).val.1 X‖ := by rw [hr]; rfl
    _ ≤ ‖(F t).val.1‖ := BoundedContinuousFunction.norm_coe_le_norm (F t).val.1.toBCF X
    _ ≤ ‖F t‖ := norm_fst_le (F t).val
    _ ≤ ‖F s‖ := hmax ht

theorem C1Tails.continuous {f : ScalarField 2} (hf : C1Tails f) : ContinuousTails f := by
  obtain ⟨F, dF, hF, -, hr, -⟩ := hf
  exact ⟨F, hF, hr⟩

theorem hasDerivWithinAt_eval {F dF : ℝ → compatible 2} {t : ℝ}
    (hF : HasDerivWithinAt F (dF t) (Ici 0) t) (X : Coord 2) :
    HasDerivWithinAt (fun s => (F s).val.1 X) ((dF t).val.1 X) (Ici 0) t := by
  have hh : HasFDerivAt (eval X) (eval X) (F t) := (eval X).hasFDerivAt (x := F t)
  exact HasFDerivAt.comp_hasDerivWithinAt (F := compatible 2) (E := ℝ) t hh hF

theorem C1Tails.cylinderC1 {f : ScalarField 2} (hf : C1Tails f) (T : ℝ) :
    ∃ G dG : ℝ → Cylinder.L2Space,
      ContinuousOn G (Icc 0 T) ∧ ContinuousOn dG (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, (fun x => G t x) =ᵐ[Cylinder.measure] (fun x => f t x.1)) ∧
      (∀ t ∈ Icc 0 T, (fun x => dG t x) =ᵐ[Cylinder.measure] (fun x => timeD f t x.1)) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt G (dG t) (Icc 0 T) t) := by
  obtain ⟨F, dF, hF, hdF, hr, hder⟩ := hf
  refine ⟨fun t => Cylinder.tailsToL2 (F t), fun t => Cylinder.tailsToL2 (dF t),
    Cylinder.tailsToL2.continuous.comp_continuousOn (hF.mono Icc_subset_Ici_self),
    Cylinder.tailsToL2.continuous.comp_continuousOn (hdF.mono Icc_subset_Ici_self), ?_, ?_, ?_⟩
  · intro t ht
    simpa only [hr] using Cylinder.coeFn_tailsToL2 (F t)
  · intro t ht
    have hr' (X : Coord 2) : (dF t).val.1 X = timeD f t X := by
      have hd : HasDerivWithinAt (fun s => f s X) ((dF t).val.1 X) (Ici 0) t := by
        simpa only [hr] using hasDerivWithinAt_eval (hder t ht.1) X
      exact (hd.derivWithin (uniqueDiffOn_Ici 0 t ht.1)).symm
    simpa only [hr'] using Cylinder.coeFn_tailsToL2 (dF t)
  · intro t ht
    have hh : HasFDerivAt Cylinder.tailsToL2 Cylinder.tailsToL2 (F t) :=
      Cylinder.tailsToL2.hasFDerivAt (x := F t)
    exact (HasFDerivAt.comp_hasDerivWithinAt (F := compatible 2) (E := Cylinder.L2Space)
      t hh (hder t ht.1)).mono Icc_subset_Ici_self

theorem continuousTails_zero : ContinuousTails (fun _ _ => 0) :=
  ⟨fun _ => 0, continuousOn_const, fun _ _ => rfl⟩

end VelocityDetection.TailSpace
end

end OAI
