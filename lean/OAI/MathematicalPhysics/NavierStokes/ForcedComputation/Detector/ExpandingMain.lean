import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFluidDetector
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingProgramParameters
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingForceBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.UniformForceBounds

namespace OAI

/-! Whole-plane velocity detection from a terminating finite program.
The program uses a single viscosity approximation to choose its schedule;
each query uses a finite prefix of the full guarded instruction graph. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set
open scoped ContDiff

def compiledExpandingForce (C : ℕ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (a : ℕ → ℚ) (ν : ℝ) : Velocity :=
  let σ := programSigma C a
  let D := programGrowth I.1 (recorderBlank I.1)
  let K := programFactor I.1 (recorderBlank I.1) (initialWordLength I)
  let p := initialCenterCode I hI σ D K
  triangularForce ν
    (expandingDrift I.1 hI.1 (recorderBlank I.1) (initialWordLength I) σ D K)
    (unitImpulse (fun j => (p j : ℝ)))

def evaluateCompiledExpandingForce (C : ℕ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (a : ℕ → ℚ) (α : List (Fin 4))
    (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let σ := programSigma C a
  let D := programGrowth I.1 (recorderBlank I.1)
  let K := programFactor I.1 (recorderBlank I.1) (initialWordLength I)
  evaluateExpandingForce I.1 hI.1 (recorderBlank I.1) (initialWordLength I)
    σ D K (initialCenterCode I hI σ D K) α a b ε hε

def compiledExpandingForceBound (C : ℕ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (a : ℕ → ℚ) (α : List (Fin 4)) (R : ℚ) : ℚ :=
  let σ := programSigma C a
  let D := programGrowth I.1 (recorderBlank I.1)
  let K := programFactor I.1 (recorderBlank I.1) (initialWordLength I)
  expandingForceBoxBound I.1 hI.1 (recorderBlank I.1) (initialWordLength I)
    σ D K (initialCenterCode I hI σ D K) α a R

theorem compiledExpandingForceBound_spec (C : ℕ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {a : ℕ → ℚ} {ν : ℝ} (ha : IsFastRealName a ν)
    (α : List (Fin 4)) (R : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) :
    ‖mixedDerivative (compiledExpandingForce C I hI a ν) α y‖ ≤
      (compiledExpandingForceBound C I hI a α R : ℝ) :=
  expandingForceBoxBound_spec I.1 hI.1 (recorderBlank I.1) (initialWordLength I)
    (programSigma_pos C a) (programGrowth_ge_one I.1 (recorderBlank I.1))
    (programFactor_nonneg I.1 (recorderBlank I.1) (initialWordLength I)) _ α ha R y hy

theorem compiledExpandingForce_effective (C : ℕ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {a : ℕ → ℚ} {ν : ℝ} (ha : IsFastRealName a ν)
    (α : List (Fin 4)) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (compiledExpandingForce C I hI a ν) α y -
      rationalVector (evaluateCompiledExpandingForce C I hI a α b ε hε)‖ ≤ (ε : ℝ) :=
  evaluateExpandingForce_spec I.1 hI.1 (recorderBlank I.1) (initialWordLength I)
    (programSigma_pos C a) (programGrowth_ge_one I.1 (recorderBlank I.1))
    (programFactor_nonneg I.1 (recorderBlank I.1) (initialWordLength I)) _ α ha hb ε hε

theorem whole_plane_velocity_detection (hE : PlaneScalarExistence)
    (hEnergy : CylinderLocalEnergyIdentity) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
      (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      let f := compiledExpandingForce C I hI a ν
      ContDiff ℝ ∞ f ∧
      (∀ α : List (Fin 4), ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖mixedDerivative f α y‖ ≤ B) ∧
      (∀ T : ℝ, ∃ K : Set Plane, IsCompact K ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, horizontalLinear x ∉ K → f (t,x) = 0) ∧
      (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
        IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative f α y -
            rationalVector (evaluateCompiledExpandingForce C I hI a α b ε hε)‖ ≤ (ε : ℝ)) ∧
      (∀ (α : List (Fin 4)) (R : ℚ) (y : SpaceTime),
        (∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) →
        ‖mixedDerivative f α y‖ ≤ (compiledExpandingForceBound C I hI a α R : ℝ)) ∧
      WholePlaneDetection ν f I := by
  obtain ⟨C, hC, hΔ⟩ := massCutoff_laplacian_bound
  refine ⟨C, hC, ?_⟩
  intro I hI ν hν a ha
  dsimp only
  let blank := recorderBlank I.1
  let m := initialWordLength I
  let σ := programSigma C a
  let D := programGrowth I.1 blank
  let K := programFactor I.1 blank m
  let p := initialCenterCode I hI σ D K
  have hσ : (0 : ℝ) < σ := by exact_mod_cast programSigma_pos C a
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast programGrowth_ge_one I.1 blank
  have hK : (0 : ℝ) ≤ K := by exact_mod_cast programFactor_nonneg I.1 blank m
  have hs := expandingDrift_smooth I.1 hI.1 blank m hσ hD hK
  refine ⟨triangularForce_smooth hs (unitImpulse_smooth (fun j => (p j : ℝ))) ν,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    simpa only [compiledExpandingForce, programGrowth_val, programFactor_val] using
      expandingForce_all_mixed_bounded I.1 hI.1 blank m hσ ν (fun j => (p j : ℝ)) α
  · intro T
    exact expandingForce_compact_on_finite_intervals I.1 hI.1 blank m hσ hD hK
      ν (fun j => (p j : ℝ)) T
  · intro α b y hb ε hε
    exact compiledExpandingForce_effective C I hI ha α hb ε hε
  · intro α R y hy
    exact compiledExpandingForceBound_spec C I hI ha α R y hy
  · have hc : (fun j => (p j : ℝ)) =
        configurationCenter I.1 hI.1 blank m σ D K 0 (finiteInitializedRecorder I hI) :=
      initialCenterCode_val I hI σ D K
    have hd := expanding_fluid_detection hE hEnergy I hI hν (Nat.cast_nonneg C)
      hσ hD hK (programSigma_budget C ha) hΔ
    simpa only [compiledExpandingForce, hc, p, σ, D, K, blank, m] using hd

end ForcedComputation.ExpandingDetector

end

end OAI
