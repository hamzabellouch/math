import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarBounds

namespace OAI

/-! Effective bounds for every mixed derivative of the compact planar
processor, with phase represented by the third coordinate. -/

noncomputable section
namespace ForcedComputation

open ShearFlows PlanarHamiltonian Set Filter
open scoped Topology ContDiff

def planeProjection : Space →L[ℝ] Plane :=
  ContinuousLinearMap.pi (fun j : Fin 2 => ContinuousLinearMap.proj j.castSucc)

@[simp] theorem planeProjection_apply (x : Space) : planeProjection x = horizontal x := by
  ext j
  fin_cases j <;> rfl

def planarMixed (f : Space → Plane) : List (Fin 3) → Space → Plane
  | [] => f
  | j :: α => fun x => fderiv ℝ (planarMixed f α) x (ShearFlows.basis j)

theorem planarMixed_eventuallyEq {f g : Space → Plane} {x : Space}
    (h : f =ᶠ[𝓝 x] g) (α : List (Fin 3)) :
    planarMixed f α =ᶠ[𝓝 x] planarMixed g α := by
  induction α with
  | nil => exact h
  | cons j α ih =>
      exact (ih.fderiv (𝕜 := ℝ)).mono
        (fun y hy => congrArg (fun A => A (ShearFlows.basis j)) hy)

theorem planarMixed_zero (α : List (Fin 3)) :
    planarMixed (fun _ : Space => (0 : Plane)) α = fun _ => 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
      simp only [planarMixed, ih, fderiv_fun_const]
      rfl

theorem planeProjection_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (α : List (Fin 3)) (x : Space) :
    planarMixed (fun y => horizontal (V (0, y))) α x =
      horizontal (mixedDerivative V (α.map Fin.succ) (0, x)) := by
  induction α generalizing x with
  | nil => rfl
  | cons j α ih =>
      have he : planarMixed (fun y => horizontal (V (0, y))) α =
          fun y => planeProjection (mixedDerivative V (α.map Fin.succ) (0, y)) :=
        funext fun y => (ih y).trans (planeProjection_apply _).symm
      rw [planarMixed, he]
      have hd := planeProjection.hasFDerivAt.comp x
        (((mixedDerivative_smooth hV (α.map Fin.succ)).differentiable (by simp)
          (0, x)).hasFDerivAt.comp x (ContinuousLinearMap.inr ℝ ℝ Space).hasFDerivAt)
      simp only [Function.comp_def] at hd
      change fderiv ℝ (fun y => planeProjection (mixedDerivative V (α.map Fin.succ) (0, y)))
        x (ShearFlows.basis j) = _
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        planeProjection_apply, List.map_cons, mixedDerivative]
      rfl

def planarField (V : ℝ → Plane → Plane) : Space → Plane :=
  letI := ShearFlows.neZeroThree
  fun x => V (x 2) (horizontal x)

theorem planarField_slice {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) :
    planarField (planarSlice H) =
      fun x => horizontal ((SpatialExpression.suspensionCode H).val (0, x)) := by
  funext x
  unfold planarField
  rw [planarSlice_eq_horizontal hH, SpatialExpression.suspensionCode_val hH hT]
  congr 2
  ext j
  fin_cases j <;> rfl

def planarMixedBound (H : FieldExpr) (α : List (Fin 3)) : ℕ :=
  (SpatialExpression.suspensionCode H).bound (α.map Fin.succ)

theorem planarMixed_slice_bound {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (α : List (Fin 3)) (x : Space) :
    ‖planarMixed (planarField (planarSlice H)) α x‖ ≤ (planarMixedBound H α : ℝ) := by
  rw [planarField_slice hH hT, planeProjection_mixed
    (VelocityExpr.smooth (SpatialExpression.suspensionCode_valid hH))]
  exact (horizontal_norm_le _).trans
    (VelocityExpr.val_bound (SpatialExpression.suspensionCode_valid hH) _ _)

namespace Recorder.Planar

theorem compactPlanarField_germ (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {x : Space}
    (hx : (horizontal x) 0 ∈ Ioo (0 : ℝ) 1 ∧
      (horizontal x) 1 ∈ Ioo (0 : ℝ) 1) :
    planarField (compactVelocity I hI) =ᶠ[𝓝 x]
      planarField (planarSlice (normalizedHamiltonian I hI)) := by
  have h₀ : {y : Space | y 0 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 x :=
    (isOpen_Ioo.preimage (continuous_apply 0)).mem_nhds hx.1
  have h₁ : {y : Space | y 1 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 x :=
    (isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds hx.2
  filter_upwards [h₀, h₁] with y hy₀ hy₁
  exact normalized_planar_field_on_chart I hI (y 2) (horizontal y) hy₀ hy₁

theorem compactPlanarField_zero_germ (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {x : Space}
    (hx : horizontal x ∉ commonSupport (normalizedPulse I hI)) :
    planarField (compactVelocity I hI) =ᶠ[𝓝 x] fun _ => 0 := by
  have hc : Continuous (horizontal : Space → Plane) := by
    rw [← show (planeProjection : Space → Plane) = horizontal from funext planeProjection_apply]
    exact planeProjection.continuous
  have hn : {y : Space | horizontal y ∉ commonSupport (normalizedPulse I hI)} ∈ 𝓝 x :=
    ((commonSupport_compact (normalizedPulse I hI)).isClosed.isOpen_compl.preimage hc).mem_nhds hx
  filter_upwards [hn] with y hy
  change compactVelocity I hI (y 2) (horizontal y) = 0
  exact image_eq_zero_of_notMem_tsupport (f := compactVelocity I hI (y 2))
    (fun hh => hy (compactVelocity_support I hI (y 2) hh))

theorem compactPlanar_mixed_bound (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (α : List (Fin 3)) (x : Space) :
    ‖planarMixed (planarField (compactVelocity I hI)) α x‖ ≤
      (planarMixedBound (normalizedHamiltonian I hI) α : ℝ) := by
  by_cases hx : horizontal x ∈ commonSupport (normalizedPulse I hI)
  · have hc := commonSupport_in_unit (normalizedPulse_inUnit I hI) hx
    rw [(planarMixed_eventuallyEq (compactPlanarField_germ I hI ⟨hc 0, hc 1⟩) α).self_of_nhds]
    exact planarMixed_slice_bound (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) α x
  · rw [(planarMixed_eventuallyEq (compactPlanarField_zero_germ I hI hx) α).self_of_nhds,
      planarMixed_zero, norm_zero]
    exact Nat.cast_nonneg _

end Recorder.Planar
end ForcedComputation

end

end OAI
