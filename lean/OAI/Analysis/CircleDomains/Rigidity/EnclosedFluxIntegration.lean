import OAI.Analysis.CircleDomains.Rigidity.AxialBandFlux
import OAI.Analysis.CircleDomains.Rigidity.AxialLineIntegral
import OAI.Analysis.CircleDomains.Rigidity.AxialChordGeometry

namespace OAI

/-! Integrating the finite-circle slice inequality. Both the exact axial
circle flux and the area integral are retained. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem enclosed_band_subset (i : Fin 2) (c : ℂ) (r R : ℝ)
    (hin : closedBall c r ⊆ ball 0 R) :
    Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) ⊆ Ioo (-R) R := by
  intro y hy
  obtain ⟨x,hx⟩ := (complexCoordinateLine_meets_closedBall i y c r).mpr hy
  have hb : ‖complexCoordinateLine i y x‖ < R := by
    simpa only [mem_ball,dist_zero_right] using hin hx
  have ht : |y| ≤ ‖complexCoordinateLine i y x‖ := by
    simpa [transverseCoordinate] using complexCoordinateLine_transverse_le i y x 0
  exact abs_lt.mp (ht.trans_lt hb)

 theorem enclosed_flux_integration {κ : Type*} [Fintype κ]
    (i : Fin 2) {F : ℂ → ℂ} (hF : Measurable F) (c : κ → ℂ) (r : κ → ℝ)
    {R B : ℝ} (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hB : 0 ≤ B)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖F z‖ ≤ B)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ ball 0 R)
    {q : ℂ → ℝ} (hq : Integrable q volume) (hq0 : ∀ z, 0 ≤ q z)
    {T : ℝ → ℝ} {C : ℝ} (hT : Integrable T volume) (hT0 : ∀ y, 0 ≤ T y)
    (hTC : (∫ y, T y) ≤ C)
    (hslice : ∀ᵐ y ∂volume, y ∈ Ioo (-R) R →
      axialBandIncrement i F 0 R y-(∑ j, axialBandIncrement i F (c j) (r j) y) ≤
        (∫ x, q (complexCoordinateLine i y x))+2*T y) :
    axialCircleFlux i F 0 R-(∑ j, axialCircleFlux i F (c j) (r j)) ≤ (∫ z, q z)+2*C := by
  have ho := axialBandIncrement_integrable hF i 0 hR hB hb
  have hi (j : κ) := axialBandIncrement_integrable hF i (c j) (hr j) hB
    (fun z hz => hb z (ball_subset_closedBall (hin j hz)))
  have hs : Integrable (fun y => ∑ j, axialBandIncrement i F (c j) (r j) y) volume :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hq' := integral_axial_slices hq i
  have ha : ∀ᵐ y ∂volume,
      axialBandIncrement i F 0 R y-(∑ j, axialBandIncrement i F (c j) (r j) y) ≤
        (∫ x, q (complexCoordinateLine i y x))+2*T y := by
    filter_upwards [hslice,volume.ae_ne (-R),volume.ae_ne R] with y hy hm hp
    by_cases h : y ∈ Ioo (-R) R
    · exact hy h
    · have hn : y ∉ Icc (-R) R := by
        rintro ⟨hl,hu⟩
        exact h ⟨lt_of_le_of_ne hl (Ne.symm hm),lt_of_le_of_ne hu hp⟩
      have hz : axialBandIncrement i F 0 R y = 0 := by
        apply indicator_of_notMem
        simpa [transverseCoordinate] using hn
      have hzj (j : κ) : axialBandIncrement i F (c j) (r j) y = 0 := by
        apply indicator_of_notMem
        exact fun hj => h (enclosed_band_subset i (c j) (r j) R (hin j) hj)
      simp only [hz,hzj,Finset.sum_const_zero,sub_zero]
      exact add_nonneg (integral_nonneg (fun x => hq0 _)) (mul_nonneg (by norm_num) (hT0 y))
  have h := integral_mono_ae (ho.sub hs) (hq'.2.1.add (hT.const_mul 2)) ha
  dsimp only [Pi.sub_apply,Pi.add_apply] at h
  rw [integral_sub ho hs,integral_finsetSum _ (fun j _ => hi j),
    integral_add hq'.2.1 (hT.const_mul 2),integral_const_mul,hq'.2.2,
    integral_axialBandIncrement i F 0 hR] at h
  simp_rw [integral_axialBandIncrement i F _ (hr _)] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hTC (by norm_num : (0 : ℝ) ≤ 2)))

end CircleDomainRigidity

end

end OAI
