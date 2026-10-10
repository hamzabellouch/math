import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInteractionPicture
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! # Exact energy identity for forced mild evolution

The identity is proved in the interaction picture and therefore holds for
arbitrary Y data and continuous Y forcing. No generator-domain assumption
or extra pair of spatial derivatives is needed.
-/

open MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

private theorem forced_component_energy_derivative (a b k s c : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (J : HomogeneousY a k →L[ℝ] Lp ℂ 2 (homogeneousSobolevMeasure s))
    (hnorm : ∀ t f, ‖J (homogeneousFreeOperator a b k t ha ha1 hk f)‖ ^ 2 =
      Real.exp (c * t) * ‖J f‖ ^ 2)
    (hinner : ∀ t f g,
      inner ℝ (J (homogeneousFreeOperator a b k t ha ha1 hk f))
        (J (homogeneousFreeOperator a b k t ha ha1 hk g)) =
        Real.exp (c * t) * inner ℝ (J f) (J g))
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun τ => ‖J (homogeneousForcedTrajectory a b k ha ha1 hk f r τ)‖ ^ 2)
      (c * ‖J (homogeneousForcedTrajectory a b k ha ha1 hk f r t)‖ ^ 2 +
        2 * inner ℝ (J (homogeneousForcedTrajectory a b k ha ha1 hk f r t)) (J (r t))) t := by
  let u := homogeneousForcedTrajectory a b k ha ha1 hk f r
  let v := fun τ => homogeneousFreeOperator a b k (-τ) ha ha1 hk (u τ)
  have hreturn (τ : ℝ) : homogeneousFreeOperator a b k τ ha ha1 hk (v τ) = u τ := by
    change homogeneousFreeOperator a b k τ ha ha1 hk
      (homogeneousFreeOperator a b k (-τ) ha ha1 hk (u τ)) = u τ
    rw [← homogeneousFreeOperator_add]
    simp only [add_neg_cancel, homogeneousFreeOperator_zero]
  have hv : HasDerivAt v (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t)) t :=
    hasDerivAt_homogeneousForcedTrajectory_pullback a b k ha ha1 hk f r hr t
  have hJ := J.hasFDerivAt.comp_hasDerivAt t hv
  have hD : HasDerivAt (fun τ => Real.exp (c * τ) * ‖J (v τ)‖ ^ 2)
      (Real.exp (c * t) * c * ‖J (v t)‖ ^ 2 + Real.exp (c * t) *
        (2 * inner ℝ (J (v t))
          (J (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t))))) t := by
    simpa only [id_eq, mul_one, Function.comp_apply, Pi.mul_apply] using!
      (((hasDerivAt_id t).const_mul c).exp).mul hJ.norm_sq
  have he (τ : ℝ) : ‖J (u τ)‖ ^ 2 = Real.exp (c * τ) * ‖J (v τ)‖ ^ 2 := by
    simpa only [hreturn] using hnorm τ (v τ)
  have hi : inner ℝ (J (u t)) (J (r t)) =
      Real.exp (c * t) * inner ℝ (J (v t))
        (J (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t))) := by
    have hcancel : homogeneousFreeOperator a b k t ha ha1 hk
        (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t)) = r t := by
      rw [← homogeneousFreeOperator_add]
      simp only [add_neg_cancel, homogeneousFreeOperator_zero]
    simpa only [hreturn, hcancel] using
      hinner t (v t) (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t))
  change HasDerivAt (fun τ => ‖J (u τ)‖ ^ 2)
    (c * ‖J (u t)‖ ^ 2 + 2 * inner ℝ (J (u t)) (J (r t))) t
  rw [show (fun τ => ‖J (u τ)‖ ^ 2) =
    (fun τ => Real.exp (c * τ) * ‖J (v τ)‖ ^ 2) from funext he]
  convert! hD using 1
  rw [he, hi]
  ring

/-- The two free rates and the exact real forcing pairing, valid for arbitrary
mild data in the faithful homogeneous Hilbert space. -/
theorem hasDerivAt_homogeneousForcedEnergy (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun τ => ‖homogeneousForcedTrajectory a b k ha ha1 hk f r τ‖ ^ 2)
      (-a * ‖homogeneousLowEnergy a k ha1 hk
          (homogeneousForcedTrajectory a b k ha ha1 hk f r t)‖ ^ 2 +
        (6 - 2 * a - k) * ‖homogeneousHighEnergy a k ha1 hk
          (homogeneousForcedTrajectory a b k ha ha1 hk f r t)‖ ^ 2 +
        2 * inner ℝ (homogeneousForcedTrajectory a b k ha ha1 hk f r t) (r t)) t := by
  have hlow := forced_component_energy_derivative a b k (6 - a) (-a) ha ha1 hk
    (homogeneousLowEnergy a k ha1 hk)
    (fun τ g => homogeneousLowEnergy_free a b k τ ha ha1 hk g)
    (fun τ g h => homogeneousLowEnergy_free_inner a b k τ ha ha1 hk g h) f r hr t
  have hhigh := forced_component_energy_derivative a b k k (6 - 2 * a - k) ha ha1 hk
    (homogeneousHighEnergy a k ha1 hk)
    (fun τ g => homogeneousHighEnergy_free a b k τ ha ha1 hk g)
    (fun τ g h => homogeneousHighEnergy_free_inner a b k τ ha ha1 hk g h) f r hr t
  convert hlow.add hhigh using 1
  · funext τ
    exact homogeneousEnergy_norm_sq a k ha1 hk _
  · rw [homogeneousEnergy_inner a k ha1 hk]
    ring

/-- Integrated energy balance for the actual forced evolution. -/
theorem homogeneousForcedEnergy_balance (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    ‖homogeneousForcedTrajectory a b k ha ha1 hk f r t‖ ^ 2 = ‖f‖ ^ 2 +
      ∫ τ in (0 : ℝ)..t,
        -a * ‖homogeneousLowEnergy a k ha1 hk
          (homogeneousForcedTrajectory a b k ha ha1 hk f r τ)‖ ^ 2 +
        (6 - 2 * a - k) * ‖homogeneousHighEnergy a k ha1 hk
          (homogeneousForcedTrajectory a b k ha ha1 hk f r τ)‖ ^ 2 +
        2 * inner ℝ (homogeneousForcedTrajectory a b k ha ha1 hk f r τ) (r τ) := by
  have hu := continuous_homogeneousForcedTrajectory a b k ha ha1 hk f r hr
  have hi : Continuous (fun τ =>
      -a * ‖homogeneousLowEnergy a k ha1 hk
        (homogeneousForcedTrajectory a b k ha ha1 hk f r τ)‖ ^ 2 +
      (6 - 2 * a - k) * ‖homogeneousHighEnergy a k ha1 hk
        (homogeneousForcedTrajectory a b k ha ha1 hk f r τ)‖ ^ 2 +
      2 * inner ℝ (homogeneousForcedTrajectory a b k ha ha1 hk f r τ) (r τ)) :=
    ((continuous_const.mul (((homogeneousLowEnergy a k ha1 hk).continuous.comp hu).norm.pow 2)).add
      (continuous_const.mul (((homogeneousHighEnergy a k ha1 hk).continuous.comp hu).norm.pow 2))).add
        (continuous_const.mul (hu.inner hr))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ => hasDerivAt_homogeneousForcedEnergy a b k ha ha1 hk f r hr τ)
    (hi.intervalIntegrable 0 t)
  rw [homogeneousForcedTrajectory_zero] at he
  linarith

end DefocusingNLS

end OAI
