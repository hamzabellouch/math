import OAI.Probability.ClassicalON.AxisRotation

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def potentialRotation (f : V → ℝ) (t : ℝ) (x : V) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  rotationExp ((t*f x) • axisC) (skewAdjoint.smul_mem _ axisC_skew)

def rotatePotential (S : SpinSystem 3 V E) (f : V → ℝ) (t : ℝ) : SpinSystem 3 V E :=
  S.rotatePins (potentialRotation f t)

def potentialOperators (S : SpinSystem 3 V E) (f : V → ℝ) : E → SpinOperator 3 :=
  fun e => S.differential f e • axisC

omit [Fintype V] [Fintype E] in
theorem gauge_potential_shift (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    S.gauge (fun e => NormedSpace.exp (u • S.potentialOperators f e)) (potentialRotation f t) =
      (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) := by
  funext e
  apply ContinuousLinearMap.ext
  intro v
  change (potentialRotation f t (S.left e)).symm
    (NormedSpace.exp (u • S.potentialOperators f e) (potentialRotation f t (S.right e) v)) = _
  simp only [potentialRotation,rotationExp_symm_apply,rotationExp_apply,potentialOperators,
    smul_smul,← neg_smul (t*f (S.left e)) axisC]
  rw [← mul_apply_eq_comp,← mul_apply_eq_comp,← exp_smul_add,← exp_smul_add]
  apply congrArg (fun r : ℝ => NormedSpace.exp (r • axisC) v)
  simp only [differential]
  ring

theorem potential_shift_Z (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    S.Z (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) =
      (S.rotatePotential f t).Z (fun e => NormedSpace.exp (u • S.potentialOperators f e)) := by
  rw [← S.gauge_potential_shift]
  exact S.Z_gauge _ _

theorem potential_shift_first (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.firstWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_twistZ (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) =
      (fun v => (S.rotatePotential f t).Z (fun e => NormedSpace.exp (v • S.potentialOperators f e))) :=
    funext fun v => S.potential_shift_Z f t v
  change HasDerivAt (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_twistZ (S.potentialOperators f) u)

theorem potential_shift_second (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).secondWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_firstVariation (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) =
      (fun v => ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) v σ ∂(S.rotatePotential f t).reference) :=
    funext fun v => S.potential_shift_first f t v
  change HasDerivAt (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_firstVariation (S.potentialOperators f) u)

theorem potential_second_response (S : SpinSystem 3 V E) (f : V → ℝ) (t : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) t σ ∂S.reference) /
      S.Z (fun e => NormedSpace.exp (t • S.potentialOperators f e)) =
      (S.rotatePotential f t).secondAxisResponse (S.differential f) (S.differential f) := by
  have hZ := S.potential_shift_Z f t 0
  have h2 := S.potential_shift_second f t 0
  simp only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] at hZ
  simp only [add_zero] at h2
  rw [hZ,h2,(S.rotatePotential f t).secondAxisResponse_integral]
  rfl

omit [Fintype V] [Fintype E] in
theorem spinRotation_potential_periodic (f : V → ℝ) (x : V)
    (h : f x=0 ∨ f x=1) (s : Spin 3) (t : ℝ) :
    spinRotation (potentialRotation f (t+2*Real.pi) x) s =
      spinRotation (potentialRotation f t x) s := by
  apply Subtype.ext
  simp only [spinRotation_val,potentialRotation,rotationExp_apply]
  rcases h with h | h
  · simp only [h,mul_zero]
  · simp only [h,mul_one,exp_axisC_periodic t]

omit [Fintype V] [Fintype E] in
theorem rotatePotential_periodic (S : SpinSystem 3 V E) (f : V → ℝ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1) :
    Function.Periodic (S.rotatePotential f) (2*Real.pi) := by
  intro t
  have hpin : (S.rotatePotential f (t+2*Real.pi)).pin = (S.rotatePotential f t).pin := by
    funext x
    apply Option.map_congr
    intro s hs
    exact spinRotation_potential_periodic f x (hP x s hs) s t
  exact congrArg (fun p => SpinSystem.mk S.left S.right S.strength p) hpin

end SpinSystem
end ClassicalON

end

end OAI
