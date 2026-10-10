import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

namespace OAI

/-! # Derivatives of smooth kinetic cutoffs along free characteristics -/

noncomputable section

open Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def characteristic (p : Velocity × Velocity) (t : ℝ) : KineticPhase :=
  ((t,p.1+t • p.2),p.2)

def transportDerivative (χ : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  fderiv ℝ χ z ((1,z.2),0)

theorem characteristic_hasDerivAt (p : Velocity × Velocity) (t : ℝ) :
    HasDerivAt (characteristic p) ((1,p.2),0) t := by
  have hx : HasDerivAt (fun s : ℝ => p.1+s • p.2) p.2 t := by
    simpa using ((hasDerivAt_id t).smul_const p.2).const_add p.1
  exact ((hasDerivAt_id t).prodMk hx).prodMk (hasDerivAt_const t p.2)

theorem hasDerivAt_along {χ : KineticPhase → ℝ} (hχ : Differentiable ℝ χ)
    (p : Velocity × Velocity) (t : ℝ) :
    HasDerivAt (fun s => χ (characteristic p s))
      (transportDerivative χ (characteristic p t)) t :=
  (hχ (characteristic p t)).hasFDerivAt.comp_hasDerivAt t (characteristic_hasDerivAt p t)

theorem characteristic_continuous (p : Velocity × Velocity) : Continuous (characteristic p) :=
  continuous_iff_continuousAt.mpr (fun t => (characteristic_hasDerivAt p t).continuousAt)

theorem transportDerivative_eq_zero {χ : KineticPhase → ℝ} {z : KineticPhase}
    (hz : z ∉ tsupport χ) : transportDerivative χ z = 0 := by
  unfold transportDerivative
  rw [fderiv_of_notMem_tsupport ℝ hz]
  rfl

theorem transportDerivative_continuous {χ : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : Continuous (transportDerivative χ) := by
  have hd : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  exact hd.clm_apply (by fun_prop)

theorem transportDerivative_hasCompactSupport {χ : KineticPhase → ℝ}
    (hχ : HasCompactSupport χ) : HasCompactSupport (transportDerivative χ) := by
  apply hχ.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hn
  exact hz (transportDerivative_eq_zero hn)

end BoltzmannNonuniqueness.TransportCutoff

end

end OAI
