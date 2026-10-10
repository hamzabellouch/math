import Mathlib
import OAI.Geometry.Cannon.Modulus.AnnularCutoffEnergy
import OAI.Geometry.Cannon.Beltrami.DirichletPullback

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane

lemma annularCutoff_energy_on {r R C : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (S : Set ℂ) :
    (∫ z in S, ‖fderiv ℝ (annularCutoff r R) z‖^2) ≤
      4*Real.pi*C^2/Real.log (R/r) := by
  let q (z : ℂ) := ‖fderiv ℝ (annularCutoff r R) z‖^2
  have hrR' : r < R := by linarith
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by simp)).norm.pow 2
  have hz (z : ℂ) (hz : z ∉ closedBall (0:ℂ) R) : q z=0 := by
    have hzn : R < ‖z‖ := by simpa using hz
    dsimp only [q]
    rw [annularCutoff_fderiv_zero_outer hr hrR' hzn]
    simp
  have hc : HasCompactSupport q := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0:ℂ) R) (Function.support_subset_iff'.mpr hz)
  have hi := hq.integrable_of_hasCompactSupport hc (μ:=volume)
  have hg : (∫ z in closedBall (0:ℂ) R, q z) = ∫ z, q z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hp : 0 ≤ᵐ[volume] q := .of_forall (fun z => sq_nonneg _)
  calc
    _ ≤ ∫ z, q z := setIntegral_le_integral hi hp
    _ = ∫ z in closedBall (0:ℂ) R, q z := hg.symm
    _ ≤ _ := annularCutoff_energy hr hrR hC0 hC

theorem annular_condenser_bound (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {r R C S δ : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    (hS : 0 < S) (hδ : 0 < δ)
    {E G : Set ℂ} (hEc : IsPreconnected E) (hGc : IsPreconnected G)
    (hEB : E ⊆ closedBall 0 S) (hGB : G ⊆ closedBall 0 S)
    (hE : ∀ z ∈ E, ‖F.symm z‖ ≤ r) (hG : ∀ z ∈ G, R ≤ ‖F.symm z‖)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdG : ∃ p ∈ G, ∃ q ∈ G, δ ≤ dist p q) :
    Real.log (R/r) ≤ 128*(4*S/δ+1)*K*Real.pi*C^2 := by
  have hrR' : r < R := by linarith
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR')
  let u := annularCutoff r R
  have hu : ContDiff ℝ 1 u := (annularCutoff_contDiff hr hrR').of_le (by simp)
  have hcap := plane_continuum_capacity (u ∘ F.symm) (hu.comp hF) hEc hGc hS hδ hEB hGB
    (fun z hz => annularCutoff_inner hr hrR' (hE z hz))
    (fun z hz => annularCutoff_outer hr hrR' (hG z hz)) hdE hdG
  have htrans := CannonBeltrami.dirichlet_pullback_le F.symm hF u hu
    (planeBox_compact S) hK hD
  have hupper := annularCutoff_energy_on hr hrR hC0 hC (F.symm '' planeBox S)
  have hc : 0 ≤ 32*(4*S/δ+1) := by positivity
  have hh := hcap.trans (mul_le_mul_of_nonneg_left (htrans.trans
    (mul_le_mul_of_nonneg_left hupper hK)) hc)
  have hid : 32*(4*S/δ+1)*(K*(4*Real.pi*C^2/Real.log (R/r))) =
      (128*(4*S/δ+1)*K*Real.pi*C^2)/Real.log (R/r) := by ring
  rw [hid] at hh
  simpa only [one_mul] using (le_div_iff₀ hL).mp hh

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
