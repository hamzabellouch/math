import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorCore

namespace OAI

/-! Translation to an arbitrary detector center. These identities preserve
the actual transition map and both variational equations. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows Set PlanarHamiltonian
open scoped ContDiff BigOperators

def translateField {A : Type*} (δ : Plane) (F : ℝ → Plane → A) : ℝ → Plane → A :=
  fun t x => F t (x + δ)

def translateTransition (δ : Plane) (Ψ : ℝ → ℝ → Plane → Plane) :
    ℝ → ℝ → Plane → Plane := fun a t x => Ψ a t (x + δ) - δ

theorem translated_smooth {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (δ : Plane) {F : ℝ → Plane → A} (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (Function.uncurry (translateField δ F)) := by
  exact hF.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))

theorem translated_periodic {A : Type*} (δ : Plane) {F : ℝ → Plane → A}
    (hp : ∀ t, PlanePeriodic (F t)) (t : ℝ) : PlanePeriodic (translateField δ F t) := by
  intro x k
  change F t ((x + fun j => (k j : ℝ)) + δ) = F t (x + δ)
  rw [add_right_comm, hp t]

theorem translated_fderiv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (δ : Plane) (F : ℝ → Plane → A) (t : ℝ) (x : Plane) :
    fderiv ℝ (translateField δ F t) x = fderiv ℝ (F t) (x + δ) :=
  fderiv_comp_add_right δ

theorem translated_second {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (δ : Plane) (F : ℝ → Plane → A) (t : ℝ) (x : Plane) :
    fderiv ℝ (fderiv ℝ (translateField δ F t)) x =
      fderiv ℝ (fderiv ℝ (F t)) (x + δ) := by
  have he : fderiv ℝ (translateField δ F t) = fun y => fderiv ℝ (F t) (y + δ) :=
    funext (translated_fderiv δ F t)
  rw [he, fderiv_comp_add_right]

theorem translated_divergence (δ : Plane) (V : ℝ → Plane → Plane) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (translateField δ V t) x =
      PlanarHamiltonian.divergence (V t) (x + δ) := by
  unfold PlanarHamiltonian.divergence spatialD
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun A : Plane →L[ℝ] ℝ => A (basis j))
    (fderiv_comp_add_right δ (f := fun y => V t y j) (x := x))

theorem transition_fderiv (δ : Plane) (Ψ : ℝ → ℝ → Plane → Plane)
    (a t : ℝ) (x : Plane) :
    fderiv ℝ (translateTransition δ Ψ a t) x = fderiv ℝ (Ψ a t) (x + δ) := by
  change fderiv ℝ (fun y => Ψ a t (y + δ) - δ) x = _
  rw [fderiv_sub_const, fderiv_comp_add_right]

theorem transition_second (δ : Plane) (Ψ : ℝ → ℝ → Plane → Plane)
    (a t : ℝ) (x : Plane) :
    fderiv ℝ (fderiv ℝ (translateTransition δ Ψ a t)) x =
      fderiv ℝ (fderiv ℝ (Ψ a t)) (x + δ) := by
  have he : fderiv ℝ (translateTransition δ Ψ a t) =
      fun y => fderiv ℝ (Ψ a t) (y + δ) := funext (transition_fderiv δ Ψ a t)
  rw [he, fderiv_comp_add_right]

theorem transition_translated {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ) (δ : Plane) :
    IsPlanarTransition (translateField δ V) (translateTransition δ Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x
    simp only [translateTransition, hΨ.initial, add_sub_cancel_right]
  · intro a t x
    have hd := (hΨ.ode a t (x + δ)).sub_const δ
    simpa only [translateTransition, translateField, sub_add_cancel] using hd
  · intro a x γ hγ hγ' t
    have hi : (γ 0 + δ) = x + δ := congrArg (fun y => y + δ) hγ
    have he := hΨ.unique a (x + δ) (fun s => γ s + δ) hi
      (fun s => (hγ' s).add_const δ) t
    simpa only [add_sub_cancel_right, translateTransition] using
      congrArg (fun y => y - δ) he

theorem variations_translated {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ) (δ : Plane) :
    PlanarVariations (translateField δ V) (translateTransition δ Ψ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    funext x
    simp only [translateTransition, hv.initial, id_eq, add_sub_cancel_right]
  · intro a t
    exact ((hv.smooth a t).comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · intro a x v t
    simpa only [transition_fderiv, translated_fderiv, translateTransition,
      sub_add_cancel] using hv.first a (x + δ) v t
  · intro a x v w t
    simpa only [transition_fderiv, transition_second, translated_fderiv,
      translated_second, translateTransition, sub_add_cancel] using
      hv.second a (x + δ) v w t

theorem backward_translated {Ψ : ℝ → ℝ → Plane → Plane}
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2)) (δ : Plane) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => translateTransition δ Ψ y.1 (-y.1) y.2) := by
  exact (hback.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))).sub contDiff_const

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
