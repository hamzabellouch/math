import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariations
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.MaterialFlow

namespace OAI

/-! Global transition maps for the actual planar differential equation.
Existence and the inverse identities below use the bounded, globally
Lipschitz finite expression, with no smooth-dependence assumption. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff NNReal

structure IsPlanarTransition (V : ℝ → Plane → Plane)
    (Ψ : ℝ → ℝ → Plane → Plane) : Prop where
  initial : ∀ a x, Ψ a 0 x = x
  ode : ∀ a t x, HasDerivAt (fun s => Ψ a s x) (V (a + t) (Ψ a t x)) t
  unique : ∀ a x (γ : ℝ → Plane), γ 0 = x →
    (∀ t, HasDerivAt γ (V (a + t) (γ t)) t) → ∀ t, γ t = Ψ a t x

theorem exists_planarTransition_of_bounds {V : ℝ → Plane → Plane} {K B : ℝ≥0}
    (hv : ∀ s, LipschitzWith K (V s))
    (hc : ∀ x, Continuous (fun s => V s x)) (hb : ∀ s x, ‖V s x‖ ≤ B) :
    ∃ Ψ, IsPlanarTransition V Ψ := by
  have hc' (a : ℝ) (x : Plane) : Continuous (fun t => V (a + t) x) := by
    have h := (hc x).comp (continuous_const.add continuous_id :
      Continuous (fun t : ℝ => a + t))
    exact h
  have hex (a : ℝ) (x : Plane) : ∃ γ : ℝ → Plane, γ 0 = x ∧
      ∀ t, HasDerivAt γ (V (a + t) (γ t)) t :=
    bounded_lipschitz_global_solution (fun t => hv (a + t)) (hc' a)
      (fun t y => hb (a + t) y) x
  choose γ hi hd using hex
  refine ⟨fun a t x => γ a x t, ⟨hi, fun a t x => hd a x t, ?_⟩⟩
  intro a x η hη hode t
  have he := ODE_solution_unique_univ (s := fun _ => univ)
    (fun s => (hv (a + s)).lipschitzOnWith)
    (fun s => ⟨hode s, mem_univ _⟩) (fun s => ⟨hd a x s, mem_univ _⟩)
    (hη.trans (hi a x).symm)
  exact congrFun he t

theorem planarSlice_continuous {H : FieldExpr} (hH : H.Valid) :
    Continuous (fun y : ℝ × Plane => planarSlice H y.1 y.2) := by
  have hi : Continuous (fun y : ℝ × Plane => atHeight y.2 y.1) := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun y : ℝ × Plane => y.2 0)
      exact (continuous_apply 0).comp continuous_snd
    · change Continuous (fun y : ℝ × Plane => y.2 1)
      exact (continuous_apply 1).comp continuous_snd
    · change Continuous (fun y : ℝ × Plane => y.1)
      exact continuous_fst
  have hh : Continuous horizontal := by
    apply continuous_pi
    intro j
    fin_cases j <;> exact continuous_apply _
  have he : (fun y : ℝ × Plane => planarSlice H y.1 y.2) =
      fun y => horizontal (SpatialExpression.suspensionField H (atHeight y.2 y.1)) :=
    funext fun y => planarSlice_eq_horizontal hH y.1 y.2
  rw [he]
  exact hh.comp ((SpatialExpression.suspensionField_smooth hH).continuous.comp hi)

theorem planarSlice_bound {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : Plane) :
    ‖planarSlice H s x‖ ≤ ((SpatialExpression.suspensionCode H).bound [] : ℝ) := by
  rw [planarSlice_eq_horizontal hH]
  apply (horizontal_norm_le _).trans
  have h := VelocityExpr.val_bound (SpatialExpression.suspensionCode_valid hH)
    [] (0, atHeight x s)
  rw [SpatialExpression.suspensionCode_val hH hT] at h
  exact h

theorem exists_planarTransition {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) :
    ∃ Ψ, IsPlanarTransition (planarSlice H) Ψ := by
  apply exists_planarTransition_of_bounds (B :=
    ((SpatialExpression.suspensionCode H).bound [] : ℝ≥0))
    (fun s => planarSlice_lipschitz hH hT s)
  · intro x
    have hi : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    have h := (planarSlice_continuous hH).comp hi
    exact h
  · exact fun s x => planarSlice_bound hH hT s x

namespace IsPlanarTransition

theorem compose {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (a s t : ℝ) (x : Plane) :
    Ψ a (s + t) x = Ψ (a + s) t (Ψ a s x) := by
  apply hΨ.unique (a + s) (Ψ a s x) (fun r => Ψ a (s + r) x)
    (by rw [add_zero])
  intro r
  have hd := (hΨ.ode a (s + r) x).scomp r ((hasDerivAt_id r).const_add s)
  simpa only [one_smul, add_assoc, Function.comp_def] using hd

theorem inverse_left {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (a t : ℝ) (x : Plane) :
    Ψ (a + t) (-t) (Ψ a t x) = x := by
  rw [← hΨ.compose, add_neg_cancel, hΨ.initial]

theorem inverse_right {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (a t : ℝ) (x : Plane) :
    Ψ a t (Ψ (a + t) (-t) x) = x := by
  have h := hΨ.inverse_left (a + t) (-t) x
  simpa only [add_neg_cancel_right, neg_neg] using h

theorem bijective {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (a t : ℝ) : Function.Bijective (Ψ a t) :=
  ⟨Function.LeftInverse.injective (hΨ.inverse_left a t),
    Function.RightInverse.surjective (hΨ.inverse_right a t)⟩

theorem perturbation {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) {K : ℝ≥0}
    (hV : ∀ s, LipschitzWith K (V s)) (a : ℝ) (x y : Plane)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (Ψ a t x) (Ψ a t y) ≤ dist x y * Real.exp ((K : ℝ) * t) := by
  have hx : Continuous (fun s => Ψ a s x) :=
    continuous_iff_continuousAt.mpr (fun s => (hΨ.ode a s x).continuousAt)
  have hy : Continuous (fun s => Ψ a s y) :=
    continuous_iff_continuousAt.mpr (fun s => (hΨ.ode a s y).continuousAt)
  have h := dist_le_of_trajectories_ODE (fun s => hV (a + s)) hx.continuousOn
    (fun s _ => (hΨ.ode a s x).hasDerivWithinAt) hy.continuousOn
    (fun s _ => (hΨ.ode a s y).hasDerivWithinAt) le_rfl t ⟨ht, le_rfl⟩
  simpa only [hΨ.initial, sub_zero] using h

end IsPlanarTransition
end ForcedComputation

end

end OAI
