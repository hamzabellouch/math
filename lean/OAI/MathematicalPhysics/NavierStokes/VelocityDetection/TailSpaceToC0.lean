import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CompactTails

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def toC0 (n : ℕ) : compatible n →L[ℝ] C₀(Coord n, ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (compatible n).subtypeL

def toL1 (n : ℕ) : compatible n →L[ℝ] Lp ℝ 1 (volume : Measure (Coord n)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (compatible n).subtypeL

@[simp] theorem toC0_apply {n : ℕ} (f : compatible n) : toC0 n f = f.val.1 := rfl

@[simp] theorem toL1_apply {n : ℕ} (f : compatible n) : toL1 n f = f.val.2 := rfl

theorem ContinuousTails.C0_rep {f : ScalarField 2} (hf : ContinuousTails f) :
    ∃ F : ℝ → C₀(Coord 2, ℝ), ContinuousOn F (Ici 0) ∧ ∀ t X, F t X = f t X := by
  obtain ⟨F, hc, hr⟩ := hf
  exact ⟨fun t => toC0 2 (F t), (toC0 2).continuous.comp_continuousOn hc, hr⟩

theorem C1Tails.L1_rep {f : ScalarField 2} (hf : C1Tails f) :
    ∃ F dF : ℝ → Lp ℝ 1 (volume : Measure (Coord 2)),
      ContinuousOn F (Ici 0) ∧ ContinuousOn dF (Ici 0) ∧
      (∀ t, (fun X => F t X) =ᵐ[volume] f t) ∧
      (∀ t ≥ 0, (fun X => dF t X) =ᵐ[volume] timeD f t) ∧
      (∀ t ≥ 0, HasDerivWithinAt F (dF t) (Ici 0) t) := by
  obtain ⟨F, dF, hc, hdc, hr, hd⟩ := hf
  refine ⟨fun t => toL1 2 (F t), fun t => toL1 2 (dF t),
    (toL1 2).continuous.comp_continuousOn hc,
    (toL1 2).continuous.comp_continuousOn hdc, ?_, ?_, ?_⟩
  · intro t
    have hh : (fun X => (F t).val.2 X) =ᵐ[volume] (fun X => (F t).val.1 X) := (F t).property
    simpa only [toL1_apply, hr] using hh
  · intro t ht
    have hh : (fun X => (dF t).val.2 X) =ᵐ[volume] (fun X => (dF t).val.1 X) := (dF t).property
    have hv (X : Coord 2) : (dF t).val.1 X = timeD f t X := by
      have he := hasDerivWithinAt_eval (hd t ht) X
      simp only [hr] at he
      exact (he.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm
    simpa only [toL1_apply, hv] using hh
  · intro t ht
    exact HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := compatible 2)
      (E := Lp ℝ 1 (volume : Measure (Coord 2))) t
      ((toL1 2).hasFDerivAt (x := F t)) (hd t ht)

end VelocityDetection.TailSpace
end

end OAI
