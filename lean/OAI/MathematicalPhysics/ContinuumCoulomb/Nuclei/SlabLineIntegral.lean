import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.DensitySynthesis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Centered-interval comparison for the actual one-coordinate Coulomb
integrals. It is the coordinatewise monotonicity step in the slab estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def centeredLineIntegral (f : ℝ → ℝ) (H x : ℝ) : ℝ :=
  ∫ t in (x-H)..(x+H), f t

theorem centeredLineIntegral_translate (f : ℝ → ℝ) (H x : ℝ) :
    centeredLineIntegral f H x = ∫ t in (-H)..H, f (x-t) := by
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [centeredLineIntegral, sub_neg_eq_add]

theorem centeredLineIntegral_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (H x : ℝ) :
    HasDerivAt (centeredLineIntegral f H) (f (x+H)-f (x-H)) x := by
  let F : ℝ → ℝ := fun a => ∫ t in (0:ℝ)..a, f t
  have hF (a : ℝ) : HasDerivAt F (f a) a :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : centeredLineIntegral f H = (fun a => F (a+H)-F (a-H)) := by
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (a+H)) (hf.intervalIntegrable 0 (a-H))).symm
  rw [he]
  simpa only [Function.comp_def, id_eq, mul_one] using
    ((hF (x+H)).comp x ((hasDerivAt_id x).add_const H)).fun_sub
      ((hF (x-H)).comp x ((hasDerivAt_id x).sub_const H))

theorem centeredLineIntegral_even (f : ℝ → ℝ) (heven : ∀ t, f (-t) = f t)
    (H x : ℝ) : centeredLineIntegral f H (-x) = centeredLineIntegral f H x := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := x-H) (b := x+H)
  simp only [heven] at h
  have ha : -(x+H) = -x-H := by ring
  have hb : -(x-H) = -x+H := by ring
  rw [ha, hb] at h
  exact h.symm

theorem centeredLineIntegral_antitone (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral f H) (Set.Ici (0:ℝ)) := by
  have hd : Differentiable ℝ (centeredLineIntegral f H) :=
    fun x => (centeredLineIntegral_hasDerivAt f hf H x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn
    hd.differentiableOn
  intro x hx
  have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici (0:ℝ))
  rw [(centeredLineIntegral_hasDerivAt f hf H x).deriv]
  apply sub_nonpos.mpr
  apply hdec
  rw [abs_of_nonneg (add_nonneg hx0 hH)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredLineIntegral_le_center (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral f H x ≤ centeredLineIntegral f H 0 := by
  have heven (t : ℝ) : f (-t) = f t := by
    apply le_antisymm
    · exact hdec t (-t) (by simp)
    · exact hdec (-t) t (by simp)
  have ha := centeredLineIntegral_antitone f hf hdec hH
  by_cases hx : 0 ≤ x
  · exact ha (Set.mem_Ici.mpr le_rfl) hx hx
  · have hn : 0 ≤ -x := by linarith
    rw [← centeredLineIntegral_even f heven H x]
    exact ha (Set.mem_Ici.mpr le_rfl) hn hn

/-- A nonsingular Coulomb line section, with the other two squared
coordinates (and optional regularization) collected in `A`. -/
def coulombLineKernel (A t : ℝ) : ℝ := (Real.sqrt (A+t^2))⁻¹

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

theorem coulombLineKernel_radial_antitone {A : ℝ} (hA : 0 < A)
    {a b : ℝ} (hab : |a| ≤ |b|) : coulombLineKernel A b ≤ coulombLineKernel A a := by
  have hs : a^2 ≤ b^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)).mpr hab
  exact inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a] : 0 < A+a^2))
    (Real.sqrt_le_sqrt (by linarith : A+a^2 ≤ A+b^2))

theorem coulombLineIntegral_antitone {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral (coulombLineKernel A) H) (Set.Ici (0:ℝ)) :=
  centeredLineIntegral_antitone _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH

theorem coulombLineIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral (coulombLineKernel A) H x ≤
      centeredLineIntegral (coulombLineKernel A) H 0 :=
  centeredLineIntegral_le_center _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH x

end ContinuumCoulomb

end

end OAI
