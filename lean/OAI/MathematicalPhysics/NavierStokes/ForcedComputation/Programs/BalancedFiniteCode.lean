import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedVelocity

namespace OAI

/-! A finite rational program for the complete balanced velocity on any
bounded time window. The repeated portion is compiled from the machine
alone; the input affects only the translation used during loading. -/

noncomputable section
namespace ForcedComputation.BalancedExpressions
open ShearFlows PlanarHamiltonian VelocityDetector Recorder.Planar Set Filter
open scoped Topology ContDiff

def substitute (σ : Fin 4 → NonperiodicExpr) : NonperiodicExpr → NonperiodicExpr
  | .const r => .const r
  | .coord j => σ j
  | .atom a e => .atom a (substitute σ e)
  | .add e f => .add (substitute σ e) (substitute σ f)
  | .mul e f => .mul (substitute σ e) (substitute σ f)

theorem substitute_val (σ : Fin 4 → NonperiodicExpr) (e : NonperiodicExpr)
    (y z : SpaceTime) (h : ∀ j, (σ j).val y = timeSpaceCoord j z) :
    (substitute σ e).val y = e.val z := by
  induction e with
  | const => rfl
  | coord j => exact h j
  | atom a e ih => exact congrArg a.profile.val ih
  | add e f ihe ihf => exact congrArg₂ (· + ·) ihe ihf
  | mul e f ihe ihf => exact congrArg₂ (· * ·) ihe ihf

def inverseCoordinates (j : Fin 4) : NonperiodicExpr :=
  .mul (.const (if j = 2 then 1/16 else 1)) (.coord j)

theorem inverseCoordinates_val (j : Fin 4) (y : SpaceTime) :
    (inverseCoordinates j).val y = timeSpaceCoord j (y.1,BalancedStretch.stretch.symm y.2) := by
  fin_cases j
  · change ((1 : ℚ) : ℝ) * y.1 = y.1
    norm_num
  · change ((1 : ℚ) : ℝ) * y.2 0 = BalancedStretch.stretch.symm y.2 0
    norm_num [BalancedStretch.coefficient]
  · change ((1/16 : ℚ) : ℝ) * y.2 1 = BalancedStretch.stretch.symm y.2 1
    norm_num [BalancedStretch.coefficient]
  · change ((1 : ℚ) : ℝ) * y.2 2 = BalancedStretch.stretch.symm y.2 2
    norm_num [BalancedStretch.coefficient]

def stretchCode (c : NonperiodicVector) : NonperiodicVector := fun j =>
  .mul (.const (if j = 1 then 16 else 1)) (substitute inverseCoordinates (c j))

theorem stretchCode_val (c : NonperiodicVector) :
    (stretchCode c).val = BalancedStretch.velocity c.val := by
  funext y j
  change (((if j = 1 then 16 else 1 : ℚ) : ℝ) * _) = _
  rw [substitute_val _ _ _ _ (fun k => inverseCoordinates_val k y)]
  simp only [BalancedStretch.velocity, BalancedStretch.push, BalancedStretch.stretch_apply,
    BalancedStretch.coefficient, NonperiodicVector.val]
  split_ifs <;> norm_num

def verticalCode : NonperiodicExpr :=
  NonperiodicExpr.composeProfile (.cutoff (-2) (-1) 1 2) (.coord 3)

theorem verticalCode_val (y : SpaceTime) :
    verticalCode.val y = BalancedBody.verticalCutoff (y.2 2) := by
  rw [verticalCode, NonperiodicExpr.val_composeProfile, ProfileExpr.val_cutoff]
  change closedCutoff ((-2 : ℚ) : ℝ) ((-1 : ℚ) : ℝ) ((1 : ℚ) : ℝ)
    ((2 : ℚ) : ℝ) (y.2 2) = _
  norm_num [BalancedBody.verticalCutoff]

def liftCode (c : NonperiodicVector) : NonperiodicVector := fun j => .mul verticalCode (c j)

theorem liftCode_val (c : NonperiodicVector) (y : SpaceTime) :
    (liftCode c).val y = BalancedBody.verticalCutoff (y.2 2) • c.val y := by
  ext j
  exact congrArg (fun r => r * (c j).val y) (verticalCode_val y)

def bodyCode (M : Alternating.Machine) (hM : M.WellFormed) (u v : ℚ) : NonperiodicVector :=
  stretchCode (liftCode (hamiltonianField (hamiltonianCode
    (normalizedPulse (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)) u v)))

theorem bodyCode_val (M : Alternating.Machine) (hM : M.WellFormed) (u v : ℚ)
    {y : SpaceTime} (hy : y.1 ∈ Icc (u : ℝ) v) :
    (bodyCode M hM u v).val y = BalancedBody.velocity M hM y := by
  rw [bodyCode, stretchCode_val]
  change BalancedStretch.stretch ((liftCode _).val
    (y.1, BalancedStretch.stretch.symm y.2)) = _
  rw [liftCode_val]
  rw [hamiltonianField_val (periodicHamiltonian_slice_smooth _ y.1)
    (fun x => hamiltonianCode_val
      (normalizedPulse_valid (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))
      u v (y := (y.1,x)) hy)]
  simp only [BalancedBody.velocity, BalancedStretch.velocity, BalancedStretch.push,
    BalancedBody.raw, CompactLift.velocity, CompactLift.spatial, triangularLift,
    horizontalLinear_eq, zero_smul, add_zero, BalancedPlanar.bodyVelocity,
    compactVelocity, periodicVelocity]

def loaderPrimitive (q : Fin 2 → ℚ) : Primitive := .translation (fun j => q j - ![4,0] j)

def loaderPotentialCode (q : Fin 2 → ℚ) : NonperiodicExpr :=
  .mul (cutoffCode BalancedLoader.rectangle 1) (primitiveCode (loaderPrimitive q))

theorem loaderPotentialCode_val (q : Fin 2 → ℚ) (y : SpaceTime) :
    (loaderPotentialCode q).val y = BalancedLoader.potential (fun j => (q j : ℝ)) (horizontal y.2) := by
  rw [loaderPotentialCode, NonperiodicExpr.val, cutoffCode_val, primitiveCode_val]
  simp only [loaderPrimitive, Primitive.potential, BalancedLoader.potential,
    BalancedLoader.direction, BalancedLoader.start, Rat.cast_sub]
  have he : (fun j => (q j : ℝ) - ((![(4 : ℚ),0] j : ℚ) : ℝ)) =
      (fun j => (q j : ℝ)) - ![4,0] := by
    funext j
    fin_cases j <;> norm_num [Pi.sub_apply]
  rw [he]

def loaderCode (q : Fin 2 → ℚ) : NonperiodicVector :=
  let p := NonperiodicExpr.composeProfile (ProfileExpr.ramp (1/8) (1/4)).diff (.coord 0)
  stretchCode (liftCode (fun j => .mul p (hamiltonianField (loaderPotentialCode q) j)))

theorem loaderCode_val (q : Fin 2 → ℚ) :
    (loaderCode q).val = BalancedLoader.velocity (fun j => (q j : ℝ)) := by
  funext y
  rw [loaderCode, stretchCode_val]
  change BalancedStretch.stretch ((liftCode _).val (y.1,BalancedStretch.stretch.symm y.2)) = _
  rw [liftCode_val]
  have hp : (NonperiodicExpr.composeProfile (ProfileExpr.ramp (1/8) (1/4)).diff
      (.coord 0)).val (y.1,BalancedStretch.stretch.symm y.2) = BalancedLoader.pulse y.1 := by
    rw [NonperiodicExpr.val_composeProfile, ProfileExpr.val_diff, ProfileExpr.val_ramp]
    change deriv (smoothRamp ((1/8 : ℚ) : ℝ) ((1/4 : ℚ) : ℝ)) y.1 = _
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  have hv : NonperiodicVector.val (fun j => (.mul
      (NonperiodicExpr.composeProfile (ProfileExpr.ramp (1/8) (1/4)).diff (.coord 0))
      (hamiltonianField (loaderPotentialCode q) j) : NonperiodicExpr))
        (y.1,BalancedStretch.stretch.symm y.2) =
      BalancedLoader.pulse y.1 • (hamiltonianField (loaderPotentialCode q)).val
        (y.1,BalancedStretch.stretch.symm y.2) := by
    funext j
    exact congrArg (fun r => r * _) hp
  rw [hv, hamiltonianField_val
    ((rectangleCutoff_smooth _ _).mul (translationPotential_smooth _))
    (fun x => loaderPotentialCode_val q (y.1,x))]
  simp only [BalancedLoader.velocity, BalancedStretch.velocity, BalancedStretch.push,
    BalancedLoader.raw, CompactLift.velocity, CompactLift.spatial, triangularLift,
    horizontalLinear_eq, zero_smul, add_zero, BalancedLoader.planarVelocity,
    BalancedLoader.spatial, map_smul]
  rfl

def activationCode (M : Alternating.Machine) (hM : M.WellFormed) : NonperiodicExpr :=
  NonperiodicExpr.composeProfile (ProfileExpr.ramp
    (BalancedBody.activationStart (BalancedBody.bodyLength M hM))
    (BalancedBody.activationFinish (BalancedBody.bodyLength M hM))) (.coord 0)

theorem activationCode_val (M : Alternating.Machine) (hM : M.WellFormed) (y : SpaceTime) :
    (activationCode M hM).val y = BalancedBody.activation M hM y.1 := by
  rw [activationCode, NonperiodicExpr.val_composeProfile, ProfileExpr.val_ramp]
  rfl

def code (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (u v : ℚ) : NonperiodicVector :=
  fun j => .add (loaderCode (BalancedPlanar.inputPosition I hI) j)
    (.mul (activationCode I.1 hI.1) (bodyCode I.1 hI.1 u v j))

theorem code_val (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (u v : ℚ)
    {y : SpaceTime} (hy : y.1 ∈ Icc (u : ℝ) v) :
    (code I hI u v).val y = BalancedVelocity.velocity I hI y := by
  have hL := congrFun (loaderCode_val (BalancedPlanar.inputPosition I hI)) y
  rw [← BalancedPlanar.inputCode_rational I hI] at hL
  have hB := bodyCode_val I.1 hI.1 u v hy
  ext j
  change (loaderCode _).val y j + (activationCode _ _).val y * (bodyCode _ _ _ _).val y j = _
  rw [hL, activationCode_val, hB]
  rfl

theorem code_germ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (u v : ℚ)
    {y : SpaceTime} (hy : y.1 ∈ Ioo (u : ℝ) v) :
    (code I hI u v).val =ᶠ[𝓝 y] BalancedVelocity.velocity I hI := by
  filter_upwards [(continuous_fst.tendsto y).eventually (Ioo_mem_nhds hy.1 hy.2)] with z hz
  exact code_val I hI u v ⟨hz.1.le,hz.2.le⟩

end ForcedComputation.BalancedExpressions

end

end OAI
