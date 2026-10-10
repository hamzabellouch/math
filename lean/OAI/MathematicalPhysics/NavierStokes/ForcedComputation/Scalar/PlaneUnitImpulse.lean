import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! The initial unit-mass vertical impulse for the expanding detector. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem smoothPulse_total_integral {a b : ℝ} (hab : a < b) :
    (∫ x, smoothPulse a b x) = 1 := by
  have hz : ∀ x, x ∉ Icc a b → smoothPulse a b x = 0 := by
    intro x hx
    by_cases hxa : x < a
    · exact smoothPulse_before hab hxa.le
    · have hax : a ≤ x := le_of_not_gt hxa
      have hbx : b < x := lt_of_not_ge (fun hxb => hx ⟨hax, hxb⟩)
      exact smoothPulse_after hab hbx.le
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  exact smoothPulse_integral hab

def impulseProfile (c x : ℝ) : ℝ := smoothPulse 0 1 (x - c + 1 / 2)

theorem impulseProfile_smooth (c : ℝ) : ContDiff ℝ ∞ (impulseProfile c) :=
  (smoothPulse_smooth 0 1).comp ((contDiff_id.sub contDiff_const).add contDiff_const)

theorem impulseProfile_nonneg (c x : ℝ) : 0 ≤ impulseProfile c x :=
  smoothPulse_nonneg (by norm_num) _

theorem impulseProfile_zero {c x : ℝ} (hx : x < c - 1 / 2 ∨ c + 1 / 2 < x) :
    impulseProfile c x = 0 := by
  rcases hx with hx | hx
  · exact smoothPulse_before (by norm_num) (by linarith)
  · exact smoothPulse_after (by norm_num) (by linarith)

theorem impulseProfile_integral (c : ℝ) : (∫ x, impulseProfile c x) = 1 := by
  have he : impulseProfile c = fun x => smoothPulse 0 1 (x + (-c + 1 / 2)) := by
    funext x
    change smoothPulse 0 1 (x - c + 1 / 2) = smoothPulse 0 1 (x + (-c + 1 / 2))
    congr 1
    ring
  rw [he, integral_add_right_eq_self]
  exact smoothPulse_total_integral (by norm_num)

def spatialImpulse (p x : Plane) : ℝ := ∏ j : Fin 2, impulseProfile (p j) (x j)

theorem spatialImpulse_smooth (p : Plane) : ContDiff ℝ ∞ (spatialImpulse p) := by
  change ContDiff ℝ ∞ (fun x : Plane => ∏ j : Fin 2, impulseProfile (p j) (x j))
  simpa only [Fin.prod_univ_two, Function.comp_def] using
    ((impulseProfile_smooth (p 0)).comp (contDiff_apply ℝ ℝ (0 : Fin 2))).mul
      ((impulseProfile_smooth (p 1)).comp (contDiff_apply ℝ ℝ (1 : Fin 2)))

theorem spatialImpulse_nonneg (p x : Plane) : 0 ≤ spatialImpulse p x :=
  Finset.prod_nonneg (fun j _ => impulseProfile_nonneg (p j) (x j))

theorem spatialImpulse_integral (p : Plane) : (∫ x, spatialImpulse p x) = 1 := by
  change (∫ x : Plane, ∏ j : Fin 2, impulseProfile (p j) (x j)) = 1
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [impulseProfile_integral, Finset.prod_const_one]

theorem spatialImpulse_support (p : Plane) : Function.support (spatialImpulse p) ⊆
    Icc (fun j => p j - 1 / 2) (fun j => p j + 1 / 2) := by
  intro x hx
  have hj (j : Fin 2) : p j - 1 / 2 ≤ x j ∧ x j ≤ p j + 1 / 2 := by
    by_contra hn
    have hz : impulseProfile (p j) (x j) = 0 := impulseProfile_zero (by
      simpa only [not_and_or, not_le] using hn)
    exact hx (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  exact ⟨fun j => (hj j).1, fun j => (hj j).2⟩

theorem spatialImpulse_compactSupport (p : Plane) : HasCompactSupport (spatialImpulse p) := by
  apply HasCompactSupport.intro (K := Icc (fun j => p j - 1 / 2) (fun j => p j + 1 / 2))
    isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (spatialImpulse_support p hn)

def unitImpulse (p : Plane) (t : ℝ) (x : Plane) : ℝ :=
  smoothPulse 0 1 t * spatialImpulse p x

theorem unitImpulse_smooth (p : Plane) : ContDiff ℝ ∞ (Function.uncurry (unitImpulse p)) :=
  ((smoothPulse_smooth 0 1).comp contDiff_fst).mul
    ((spatialImpulse_smooth p).comp contDiff_snd)

theorem unitImpulse_nonneg (p : Plane) (t : ℝ) (x : Plane) : 0 ≤ unitImpulse p t x :=
  mul_nonneg (smoothPulse_nonneg (by norm_num) t) (spatialImpulse_nonneg p x)

theorem unitImpulse_mass (p : Plane) (t : ℝ) : (∫ x, unitImpulse p t x) = smoothPulse 0 1 t := by
  change (∫ x, smoothPulse 0 1 t * spatialImpulse p x) = smoothPulse 0 1 t
  rw [integral_const_mul, spatialImpulse_integral, mul_one]

end ForcedComputation.ExpandingDetector

end

end OAI
