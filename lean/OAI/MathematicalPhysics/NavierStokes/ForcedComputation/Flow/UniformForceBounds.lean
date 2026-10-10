import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.UniformJetBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGlobalBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneUnitImpulse

namespace OAI

/-! Every mixed derivative of the actual whole-plane force is bounded
for all time. The source and the complete drift are prescribed first. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector Recorder Set
open scoped ContDiff BigOperators

theorem UniformJets.mixed {U : Velocity} (hU : ContDiff ℝ ∞ U)
    (hb : UniformJets U) (α : List (Fin 4)) : UniformJets (mixedDerivative U α) := by
  induction α with
  | nil => exact hb
  | cons j α ih => exact ih.directional (mixedDerivative_smooth hU α) (spaceTimeDirection j)

theorem UniformJets.mixed_bound {U : Velocity} (hU : ContDiff ℝ ∞ U)
    (hb : UniformJets U) (α : List (Fin 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖mixedDerivative U α y‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := (hb.mixed hU α) 0
  exact ⟨B,hB,fun y => by simpa only [norm_iteratedFDeriv_zero] using hbound y⟩

theorem UniformJets.force {U : Velocity} (hU : ContDiff ℝ ∞ U)
    (hb : UniformJets U) (ν : ℝ) : UniformJets (force ν U) := by
  have hl : UniformJets (fun y => ∑ j : Fin 3, mixedDerivative U [j.succ,j.succ] y) :=
    UniformJets.sum (fun j => mixedDerivative_smooth hU _) (fun j => hb.mixed hU _)
  have hls : ContDiff ℝ ∞ (fun y => ∑ j : Fin 3, mixedDerivative U [j.succ,j.succ] y) :=
    ContDiff.sum (fun j _ => mixedDerivative_smooth hU _)
  have he : ShearFlows.force ν U = mixedDerivative U [0] -
      ν • (fun y => ∑ j : Fin 3, mixedDerivative U [j.succ,j.succ] y) := by
    funext y
    exact force_eq_mixed hU ν y
  rw [he]
  exact (hb.mixed hU [0]).sub (mixedDerivative_smooth hU [0]) (hls.const_smul ν)
    (hl.const_smul hls ν)

theorem UniformJets.convection {U : Velocity} (hU : ContDiff ℝ ∞ U)
    (hb : UniformJets U) : UniformJets (convectiveField U) := by
  have hcoord (j : Fin 3) : UniformJets (fun y => U y j) :=
    hb.linear_left hU (ContinuousLinearMap.proj j)
  have hcoords (j : Fin 3) : ContDiff ℝ ∞ (fun y => U y j) :=
    (contDiff_apply ℝ ℝ j).comp hU
  have he : convectiveField U = fun y => ∑ j : Fin 3, U y j • mixedDerivative U [j.succ] y :=
    funext (convectiveField_eq_mixed hU)
  rw [he]
  exact UniformJets.sum
    (fun j => (hcoords j).smul (mixedDerivative_smooth hU [j.succ]))
    (fun j => (hcoord j).smul (hcoords j) (mixedDerivative_smooth hU [j.succ]) (hb.mixed hU _))

theorem UniformJets.residual {U : Velocity} (hU : ContDiff ℝ ∞ U)
    (hb : UniformJets U) (ν : ℝ) : UniformJets (residual ν U) := by
  rw [residual_eq_force_add]
  exact (hb.force hU ν).add (force_smooth hU ν) (convectiveField_smooth hU) (hb.convection hU)

private def horizontalTimeProjection : SpaceTime →L[ℝ] (ℝ × Plane) :=
  (ContinuousLinearMap.fst ℝ ℝ Space).prod
    (horizontalLinear.comp (ContinuousLinearMap.snd ℝ ℝ Space))

theorem unitImpulse_compactSupport (p : Plane) :
    HasCompactSupport (Function.uncurry (unitImpulse p)) := by
  let K : Set (ℝ × Plane) := Icc 0 1 ×ˢ tsupport (spatialImpulse p)
  apply HasCompactSupport.intro (K := K)
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod (spatialImpulse_compactSupport p).isCompact)
  rintro ⟨t,x⟩ hx
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hz : spatialImpulse p x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ⟨ht,h⟩)
    simp only [Function.uncurry_apply_pair, unitImpulse, hz, mul_zero]
  · have hz : smoothPulse 0 1 t = 0 := by
      by_cases ht0 : t ≤ 0
      · exact smoothPulse_before (by norm_num) ht0
      · exact smoothPulse_after (by norm_num) (by
          have ht0' : 0 ≤ t := le_of_lt (lt_of_not_ge ht0)
          by_contra hn
          exact ht ⟨ht0',le_of_lt (lt_of_not_ge hn)⟩)
    simp only [Function.uncurry_apply_pair, unitImpulse, hz, zero_mul]

theorem expandingForce_all_mixed_bounded (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) (p : Plane) (α : List (Fin 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
      ‖mixedDerivative (triangularForce ν (expandingDrift M hM blank m σ
        (workGrowth M blank) (workFactor M blank m)) (unitImpulse p)) α y‖ ≤ B := by
  let a := expandingDrift M hM blank m σ (workGrowth M blank) (workFactor M blank m)
  have ha := expandingDrift_smooth M hM blank m hσ (workGrowth_ge_one M blank)
    (workFactor_nonneg M blank m)
  have hab : UniformJets (Function.uncurry a) :=
    expandingDrift_all_jets_bounded M hM blank m hσ
  have hb : UniformJets (triangularVelocity a (fun _ _ => 0)) := by
    have hcomp := hab.linear_right ha horizontalTimeProjection
    have hcompS := ha.comp horizontalTimeProjection.contDiff
    have h := hcomp.linear_left hcompS planeInclusion
    have he : triangularVelocity a (fun _ _ => 0) =
        planeInclusion ∘ (Function.uncurry a ∘ horizontalTimeProjection) := by
      funext y
      simp [Function.comp_def, horizontalTimeProjection, triangularVelocity, triangularLift]
    rw [he]
    exact h
  have hs : UniformJets (Function.uncurry (unitImpulse p)) := by
    intro n
    obtain ⟨C,hC,hbound⟩ := (unitImpulse_compactSupport p).exists_bound_iteratedFDeriv
      (unitImpulse_smooth p) n
    exact ⟨C,hC,fun y => hbound n le_rfl y⟩
  have hsource : UniformJets (triangularVelocity (fun _ _ => 0) (unitImpulse p)) := by
    have hb := hs.linear_right (unitImpulse_smooth p) horizontalTimeProjection
    have hbS := (unitImpulse_smooth p).comp horizontalTimeProjection.contDiff
    let L : ℝ →L[ℝ] Space := (1 : ℝ →L[ℝ] ℝ).smulRight (basis 2)
    have h := hb.linear_left hbS L
    have he : triangularVelocity (fun _ _ => 0) (unitImpulse p) =
        L ∘ (Function.uncurry (unitImpulse p) ∘ horizontalTimeProjection) := by
      funext y
      simp [Function.comp_def, horizontalTimeProjection, triangularVelocity, triangularLift, L]
    rw [he]
    exact h
  have hforce : UniformJets (triangularForce ν a (unitImpulse p)) := by
    rw [triangularForce_eq_residual ha]
    exact (hb.residual (triangularVelocity_smooth ha contDiff_const) ν).add
      (residual_smooth (triangularVelocity_smooth ha contDiff_const) ν)
      (triangularVelocity_smooth contDiff_const (unitImpulse_smooth p)) hsource
  exact hforce.mixed_bound (triangularForce_smooth ha (unitImpulse_smooth p) ν) α

end ForcedComputation.VelocityDetector

end

end OAI
