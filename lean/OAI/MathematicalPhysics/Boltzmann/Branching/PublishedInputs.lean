import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace OAI

/-!
# Published analytic input for periodic hard-sphere nonuniqueness

`GLPS1988Proposition3` expresses the velocity-localized, time-dependent specialization of Proposition 3
of F. Golse, P.-L. Lions, B. Perthame and R. Sentis, "Regularity of the moments of the solution of
a transport equation", J. Functional Analysis 76 (1988), 110–125, pp. 115–116,
DOI: 10.1016/0022-1236(88)90051-1. The passage to evolution equations is explained in their
Remark (2), p. 119. In their notation, the velocity measure is supported on velocities `(1,v)`;
compact velocity support supplies their nonconcentration condition (2.14).

This compactness statement applies to uniformly integrable sources with bounded velocity
support, independently of the cap and branching constructions.

The global continuation input is Theorem 4.1 of C. D. Levermore and N. Masmoudi,
"From the Boltzmann equation to an incompressible Navier–Stokes–Fourier system",
Arch. Rational Mech. Anal. 196 (2010), 753–809, pp. 765–767,
DOI: 10.1007/s00205-009-0254-5. The elementary entropy estimate converts that
continuation theorem to separate gain and loss integrability.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

abbrev Velocity := EuclideanSpace ℝ (Fin 3)
abbrev SpaceTime := ℝ × Velocity
abbrev KineticPhase := SpaceTime × Velocity

/-- The damped free-transport resolvent, with the incoming characteristic parametrization. -/
def transportResolvent (r : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  ∫ s in Ici (0 : ℝ), Real.exp (-s) * r ((z.1.1 - s, z.1.2 - s • z.2), z.2)

/-- A velocity average of the damped free-transport resolvent. -/
def resolventAverage (r : KineticPhase → ℝ) (ψ : Velocity → ℝ) (z : SpaceTime) : ℝ :=
  ∫ v, ψ v * transportResolvent r (z, v)

/-- Local `L¹` convergence is stated with the extended `L¹` seminorm, so that an undefined
Bochner integral cannot make a nonintegrable error appear to have zero norm. -/
def LocalL1Converges (f : ℕ → SpaceTime → ℝ) (g : SpaceTime → ℝ) : Prop :=
  LocallyIntegrable g ∧
    ∀ K : Set SpaceTime, IsCompact K →
      Tendsto (fun n => eLpNorm (fun z => f n z - g z) 1 (volume.restrict K))
        atTop (𝓝 0)

/-- A sequential specialization of GLPS (1988), Proposition 3, with the evolution-equation
extension in Remark (2), p. 119. Boundedness and uniform integrability are both contained in
`UniformIntegrable`. The hypothesis has no relation to the novel branching construction. -/
def GLPS1988Proposition3 : Prop :=
  ∀ (r : ℕ → KineticPhase → ℝ) (R : ℝ), 0 < R →
    (∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), R < ‖z.2‖ → r n z = 0) →
    UniformIntegrable r 1 volume →
    ∀ ψ : Velocity → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ (φ : ℕ → ℕ) (g : SpaceTime → ℝ), StrictMono φ ∧
        LocalL1Converges (fun n => resolventAverage (r (φ n)) ψ) g

/-- The entropy-production integrand for strictly positive incoming and outgoing products. -/
def entropyProduction (A B : ℝ) : ℝ := (A - B) * Real.log (A / B)

theorem entropyProduction_nonneg {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    0 ≤ entropyProduction A B := by
  by_cases h : B ≤ A
  · exact mul_nonneg (sub_nonneg.mpr h)
      (Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using h)))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))
      (Real.log_nonpos (div_nonneg hA.le hB.le)
        ((div_le_one hB).mpr (le_of_not_ge h)))

/-- The positive-product case of the entropy bound used in the manuscript's continuation
argument: gain is controlled by twice loss and entropy production. Zero-product boundary values
are extended-real values in the Boltzmann dissipation and are not encoded using `Real.log 0`. -/
theorem gain_le_loss_add_entropy {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A ≤ 2 * B + (2 / Real.log 2) * entropyProduction A B := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod := entropyProduction_nonneg hA hB
  by_cases h : A ≤ 2 * B
  · exact h.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hprod))
  · have hAB : A / 2 ≤ A - B := by linarith
    have hratio : 2 ≤ A / B := (le_div_iff₀ hB).mpr (by linarith)
    have hlogratio : Real.log 2 ≤ Real.log (A / B) :=
      Real.log_le_log (by norm_num) hratio
    have hmul : A / 2 * Real.log 2 ≤ entropyProduction A B := by
      exact mul_le_mul hAB hlogratio hlog.le (by linarith)
    have hgain : A ≤ (2 / Real.log 2) * entropyProduction A B := by
      calc
        A = (2 / Real.log 2) * (A / 2 * Real.log 2) := by
          field_simp
        _ ≤ (2 / Real.log 2) * entropyProduction A B :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
    exact hgain.trans (le_add_of_nonneg_left (by positivity))

/-! ## Scalar estimates in the reference branching process

The uniform distribution of a spherical coordinate gives a lower bound for
retention in the speed-five ball and a positive branching potential.
-/

/-- The squared child speed cannot exceed `s + 1` if its spherical coordinate is in `[-1,1]`
and its radial coefficient lies between zero and `s + 1`. -/
theorem child_energy_le {s R Z : ℝ} (hR : 0 ≤ R) (hRs : R ≤ s + 1)
    (hZ : Z ≤ 1) : (s + 1 + R * Z) / 2 ≤ s + 1 := by
  have hRZ : R * Z ≤ R := by nlinarith
  linarith

/-- For squared parent speed at most `25`, the upper-tail probability from the uniform
`[-1,1]` coordinate is at most `1/26`. The formula applies when its radial coefficient is positive;
the deterministic zero-radius case is handled by `child_energy_le`. -/
theorem reference_exit_probability_le {s R : ℝ} (hs : s ≤ 25) (hR : 0 < R)
    (hRs : R ≤ s + 1) :
    max 0 ((1 / 2 : ℝ) + (s - 49) / (2 * R)) ≤ 1 / 26 := by
  have hdiv : (s - 49) / (2 * R) ≤ -(6 / 13 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * R)).mpr
    nlinarith
  exact max_le (by norm_num) (by linarith)

/-- The retained probability in the speed-five ball has the value used in Section 9. -/
theorem reference_retention_probability_ge {s R : ℝ} (hs : s ≤ 25) (hR : 0 < R)
    (hRs : R ≤ s + 1) :
    25 / 26 ≤ 1 - max 0 ((1 / 2 : ℝ) + (s - 49) / (2 * R)) := by
  have h := reference_exit_probability_le hs hR hRs
  linarith

/-- The branching potential is bounded below by `48π/13`, as soon as the scalar retention
bound and the minimal two-beam collision frequency have been established. -/
theorem reference_potential_ge {p ν : ℝ} (hp : 25 / 26 ≤ p)
    (hν : 4 * Real.pi ≤ ν) : 48 * Real.pi / 13 ≤ (2 * p - 1) * ν := by
  have hcoef : (12 / 13 : ℝ) ≤ 2 * p - 1 := by linarith
  calc
    48 * Real.pi / 13 = (12 / 13 : ℝ) * (4 * Real.pi) := by ring
    _ ≤ (2 * p - 1) * ν :=
      mul_le_mul hcoef hν (by positivity) (by linarith)

/-- The associated single-particle jump rate is bounded by `48π`. -/
theorem reference_rate_le {p ν : ℝ} (hp : p ≤ 1)
    (hν : ν ≤ 24 * Real.pi) (hν0 : 0 ≤ ν) : 2 * p * ν ≤ 48 * Real.pi := by
  calc
    2 * p * ν ≤ 2 * 1 * (24 * Real.pi) :=
      mul_le_mul (by linarith) hν hν0 (by positivity)
    _ = 48 * Real.pi := by ring

end BoltzmannNonuniqueness.Published

end

end OAI
