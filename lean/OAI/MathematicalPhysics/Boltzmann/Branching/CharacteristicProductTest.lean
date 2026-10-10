import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCoordinates
import OAI.MathematicalPhysics.Boltzmann.Branching.HotChartHomeomorph

namespace OAI

section

/-! # Smooth compact tests in free-characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

abbrev CharacteristicPhase := ℝ × (Velocity × Velocity)

theorem characteristicEquiv_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (characteristicEquiv : CharacteristicPhase → Published.KineticPhase) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : CharacteristicPhase => ((z.1,z.2.1+z.1 • z.2.2),z.2.2))
  fun_prop

theorem characteristicEquiv_symm_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (characteristicEquiv.symm : Published.KineticPhase → CharacteristicPhase) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : Published.KineticPhase =>
    (z.1.1,(z.1.2-z.1.1 • z.2,z.2)))
  fun_prop

def characteristicHomeomorph : CharacteristicPhase ≃ₜ Published.KineticPhase where
  toEquiv := characteristicEquiv.toEquiv
  continuous_toFun := characteristicEquiv_contDiff.continuous
  continuous_invFun := characteristicEquiv_symm_contDiff.continuous

def testPullback (ψ : CharacteristicPhase → ℝ) : Published.KineticPhase → ℝ :=
  ψ ∘ characteristicEquiv.symm

theorem testPullback_contDiff {ψ : CharacteristicPhase → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : ContDiff ℝ (⊤ : ℕ∞) (testPullback ψ) :=
  hψ.comp characteristicEquiv_symm_contDiff

theorem testPullback_compact {ψ : CharacteristicPhase → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (testPullback ψ) :=
  hψ.comp_homeomorph characteristicHomeomorph.symm

def timeDerivative (ψ : CharacteristicPhase → ℝ) (z : CharacteristicPhase) : ℝ :=
  fderiv ℝ ψ z (1,0)

theorem timeDerivative_continuous {ψ : CharacteristicPhase → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Continuous (timeDerivative ψ) := by
  exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem testPullback_along (ψ : CharacteristicPhase → ℝ) (p : Velocity × Velocity) (t : ℝ) :
    testPullback ψ (TransportCutoff.characteristic p t) = ψ (t,p) := by
  change ψ (characteristicEquiv.symm (characteristicEquiv (t,p))) = ψ (t,p)
  rw [MeasurableEquiv.symm_apply_apply]

theorem transportDerivative_testPullback {ψ : CharacteristicPhase → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Published.KineticPhase) :
    transportDerivative (testPullback ψ) z = timeDerivative ψ (characteristicEquiv.symm z) := by
  obtain ⟨⟨t,p⟩,rfl⟩ := characteristicEquiv.surjective z
  have h₁ := hasDerivAt_along ((testPullback_contDiff hψ).differentiable (by simp)) p t
  have he : (fun s => testPullback ψ (TransportCutoff.characteristic p s)) = fun s => ψ (s,p) := by
    funext s
    exact testPullback_along ψ p s
  rw [he] at h₁
  have h₂ : HasDerivAt (fun s : ℝ => ψ (s,p)) (timeDerivative ψ (t,p)) t := by
    exact (hψ.differentiable (by simp) (t,p)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))
  simp only [MeasurableEquiv.symm_apply_apply]
  change transportDerivative (testPullback ψ) (TransportCutoff.characteristic p t) = timeDerivative ψ (t,p)
  exact h₁.unique h₂

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Time and phase test products in characteristic coordinates -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def timePhaseTest (θ : ℝ → ℝ) (φ : Velocity × Velocity → ℝ) : CharacteristicPhase → ℝ :=
  fun z => θ z.1*φ z.2

theorem timePhaseTest_contDiff {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePhaseTest θ φ) :=
  (hθ.comp contDiff_fst).mul (hφ.comp contDiff_snd)

theorem timePhaseTest_support (θ : ℝ → ℝ) (φ : Velocity × Velocity → ℝ) :
    tsupport (timePhaseTest θ φ) ⊆ tsupport θ ×ˢ tsupport φ := by
  apply closure_minimal _ ((isClosed_tsupport θ).prod (isClosed_tsupport φ))
  intro z hz
  change θ z.1*φ z.2 ≠ 0 at hz
  exact ⟨subset_tsupport θ (mul_ne_zero_iff.mp hz).1,
    subset_tsupport φ (mul_ne_zero_iff.mp hz).2⟩

theorem timePhaseTest_compact {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : HasCompactSupport θ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (timePhaseTest θ φ) :=
  (hθ.isCompact.prod hφ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (timePhaseTest_support θ φ)

theorem timeDerivative_timePhaseTest {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : CharacteristicPhase) : timeDerivative (timePhaseTest θ φ) z = deriv θ z.1*φ z.2 := by
  have h₁ : HasDerivAt (fun s : ℝ => timePhaseTest θ φ (s,z.2))
      (timeDerivative (timePhaseTest θ φ) z) z.1 := by
    exact ((timePhaseTest_contDiff hθ hφ).differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact h₁.unique ((hθ.differentiable (by simp) z.1).hasDerivAt.mul_const (φ z.2))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
