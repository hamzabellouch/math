import OAI.Analysis.Mahler.ConformalInjectivity
import OAI.Analysis.Mahler.AngularStrip
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

namespace OAI

/-! The biholomorphic map and its inverse.
The vertical interval property and P_m estimates are not asserted here. -/

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace MahlerConformal

def Omega : Set ℂ := F '' ball (0 : ℂ) 1
def inverseF : ℂ → ℂ := Function.invFunOn F (ball (0 : ℂ) 1)

lemma inverseF_mem {u : ℂ} (hu : u ∈ Omega) : inverseF u ∈ ball (0 : ℂ) 1 :=
  Function.invFunOn_mem hu

lemma inverseF_right {u : ℂ} (hu : u ∈ Omega) : F (inverseF u) = u :=
  Function.invFunOn_eq hu

lemma inverseF_left {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : inverseF (F w) = w :=
  F_injOn_disk.leftInvOn_invFunOn hw

lemma hasStrictDerivAt_F {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasStrictDerivAt F (deriv F w) w :=
  ((differentiableOn_F.analyticAt (isOpen_ball.mem_nhds hw)).contDiffAt (n := 1)).hasStrictDerivAt
    (by norm_num)

theorem isOpen_Omega : IsOpen Omega := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨w, hw, rfl⟩
  rw [← (hasStrictDerivAt_F hw).map_nhds_eq (deriv_F_ne_zero (by simpa using hw))]
  change F ⁻¹' Omega ∈ 𝓝 w
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hw)
  intro z hz
  exact ⟨z, hz, rfl⟩

theorem isConnected_Omega : IsConnected Omega := by
  have hc : IsConnected (ball (0 : ℂ) 1) :=
    ⟨⟨0, by simp⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  exact hc.image F differentiableOn_F.continuousOn

/-- The selected inverse is holomorphic on its exact image domain, with the
reciprocal derivative. Its local inverse hypotheses follow from proved injectivity. -/
theorem hasDerivAt_inverseF {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt inverseF (deriv F (inverseF u))⁻¹ u := by
  have hw := inverseF_mem hu
  have hl : ∀ᶠ w in 𝓝 (inverseF u), inverseF (F w) = w := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w hw
    exact inverseF_left hw
  have hd := (hasStrictDerivAt_F hw).to_local_left_inverse
    (deriv_F_ne_zero (by simpa using hw)) hl
  rw [inverseF_right hu] at hd
  exact hd.hasDerivAt

theorem differentiableOn_inverseF : DifferentiableOn ℂ inverseF Omega :=
  fun _ hu => (hasDerivAt_inverseF hu).differentiableAt.differentiableWithinAt

theorem inverseF_deriv_ne_zero {u : ℂ} (hu : u ∈ Omega) : deriv inverseF u ≠ 0 := by
  rw [(hasDerivAt_inverseF hu).deriv]
  exact inv_ne_zero (deriv_F_ne_zero (by simpa using inverseF_mem hu))

theorem Omega_conj {u : ℂ} (hu : u ∈ Omega) : starRingEnd ℂ u ∈ Omega := by
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa using hw

theorem inverseF_conj {u : ℂ} (hu : u ∈ Omega) :
    inverseF (starRingEnd ℂ u) = starRingEnd ℂ (inverseF u) := by
  apply F_injOn_disk (inverseF_mem (Omega_conj hu)) (by simpa using inverseF_mem hu)
  rw [inverseF_right (Omega_conj hu), F_conj, inverseF_right hu]

theorem zero_mem_Omega : (0 : ℂ) ∈ Omega := ⟨0, by simp, F_zero⟩

theorem inverseF_zero : inverseF 0 = 0 := by
  simpa only [F_zero] using inverseF_left (w := 0) (by simp)

theorem inverseF_eq_zero_iff {u : ℂ} (hu : u ∈ Omega) : inverseF u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [← inverseF_right hu, h, F_zero]
  · intro h
    rw [h, inverseF_zero]

/-- The biholomorphic-map property of F.
No vertical fiber property or primitive estimate is hidden in this statement. -/
theorem conformal_biholomorphism :
    IsOpen Omega ∧ IsConnected Omega ∧
    Set.BijOn F (ball (0 : ℂ) 1) Omega ∧
    DifferentiableOn ℂ F (ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ inverseF Omega ∧
    Set.LeftInvOn inverseF F (ball (0 : ℂ) 1) ∧ Set.RightInvOn inverseF F Omega ∧
    F 0 = 0 ∧ deriv F 0 ≠ 0 ∧
    Complex.re '' Omega = Ioo (-1 : ℝ) 1 ∧ Set.MapsTo (starRingEnd ℂ) Omega Omega := by
  exact ⟨isOpen_Omega, isConnected_Omega,
    ⟨mapsTo_image _ _, F_injOn_disk, surjOn_image F _⟩,
    differentiableOn_F, differentiableOn_inverseF, fun _ => inverseF_left,
    fun _ => inverseF_right, F_zero, deriv_F_ne_zero (by simp), image_re_F_disk,
    fun _ => Omega_conj⟩

end MahlerConformal

end

end OAI
