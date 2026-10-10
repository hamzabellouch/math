import OAI.MeasureTheory.Falconer.Estimates.QuadraticBudget
import OAI.MeasureTheory.Falconer.Fourier.LocalStationaryJets

namespace OAI

/-! # Smooth fixed-patch extensions of actual stationary jets

The mask is one on the prepared inner cap and vanishes near the antipodal
singularity of the chosen frame. No global spherical differential operator
is assumed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryPatchMask (m : ℕ) : Space (m+3) → ℝ :=
  poleCutoff (gnomonicChart (0 : Space (m+2)))

theorem stationaryPatchMask_contDiff (m : ℕ) : ContDiff ℝ ∞ (stationaryPatchMask m) :=
  poleCutoff_contDiff _

theorem stationaryPatchMask_one (m : ℕ) (x : Space (m+3))
    (hx : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    stationaryPatchMask m x = 1 := poleCutoff_one _ x hx

theorem stationary_patch_ne_antipode (m : ℕ) {x : Space (m+3)}
    (hx : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4) :
    (gnomonicChart (0 : Space (m+2)) : Space (m+3))+x ≠ 0 := by
  intro he
  have hx' : x = -(gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he
  rw [hx',norm_sub_rev,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm] at hx
  norm_num at hx

theorem stationaryPatchMask_support (m : ℕ) :
    tsupport (stationaryPatchMask m) =
      closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4) :=
  (capBump (1/4) (by norm_num) (gnomonicChart (0 : Space (m+2)))).tsupport_eq

noncomputable def maskedStationaryCoefficient (m j : ℕ) (B : Space (m+3) → ℂ)
    (x : Space (m+3)) : ℂ :=
  (stationaryPatchMask m x : ℂ)*actualStationaryCoefficient m j B x

theorem maskedStationaryCoefficient_contDiff (m j : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (maskedStationaryCoefficient m j B) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (stationaryPatchMask m)
  · have hnear : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
      simpa only [stationaryPatchMask_support,mem_closedBall,dist_eq_norm] using hx
    exact ((Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).contDiffAt).mul
      (actualStationaryCoefficient_contDiffAt m j hB (stationary_patch_ne_antipode m hnear))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change stationaryPatchMask m y = (0 : ℝ) at hy
    simp only [maskedStationaryCoefficient,hy,Complex.ofReal_zero,zero_mul]

theorem quadraticJetCoefficient_zero_amplitude (n j : ℕ) :
    quadraticJetCoefficient j (fun _ : Space n => (0 : ℂ)) = 0 := by
  have hz : (Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ)) (fun _ => 0) =
      (fun _ => 0) := InnerProductSpace.laplacian_const
  simp only [quadraticJetCoefficient,Function.iterate_fixed hz,mul_zero]

theorem actualStationaryCoefficient_zero_amplitude (m j : ℕ) (x : Space (m+3)) :
    actualStationaryCoefficient m j (fun _ => 0) x = 0 := by
  have he : (fun u => unmaskedStationaryAmplitude m (fun _ => 0) (x,u)) =
      (fun _ : Space (m+2) => (0 : ℂ)) := by
    funext u
    simp only [unmaskedStationaryAmplitude,mul_zero]
  change quadraticJetCoefficient j _ = 0
  rw [he]
  exact quadraticJetCoefficient_zero_amplitude _ _

theorem maskedStationaryCoefficient_eq (m j : ℕ) (B : Space (m+3) → ℂ)
    (x : Space (m+3)) (hx : stationaryPatchMask m x = 1) :
    maskedStationaryCoefficient m j B x = actualStationaryCoefficient m j B x := by
  simp only [maskedStationaryCoefficient,hx,Complex.ofReal_one,one_mul]

end Falconer

end OAI
