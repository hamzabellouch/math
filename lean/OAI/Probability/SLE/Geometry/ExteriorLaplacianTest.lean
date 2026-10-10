import OAI.Probability.SLE.Geometry.CompactLaplacianIntegral
import OAI.Probability.SLE.Geometry.ConformalLaplacian

namespace OAI

/-! A compactly supported quadratic test near the omitted set of an
exterior conformal map. Its Laplacian has nonpositive integral over the
image domain. -/
noncomputable section
open Set Filter Metric Function MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma complex_laplacian_norm_sq (z : ℂ) : (Δ (fun w : ℂ => ‖w‖^2)) z=4 := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := 2 • innerSL ℝ
  have hd : fderiv ℝ (fun w : ℂ => ‖w‖^2)=L := fderiv_norm_sq
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,hd,L.fderiv]
  simp only [L,two_smul,add_apply]
  change (inner ℝ (1:ℂ) 1+inner ℝ (1:ℂ) 1)+(inner ℝ Complex.I Complex.I+inner ℝ Complex.I Complex.I)=4
  simp only [real_inner_self_eq_norm_sq,norm_one,Complex.norm_I]
  norm_num

lemma exists_compact_quadratic_test (K : Set ℂ) (hK : IsCompact K) :
    ∃ u : ℂ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      (∀ z∈K, u =ᶠ[𝓝 z] (fun w => ‖w‖^2)) ∧
      (∀ z∈K, (Δ u) z=4) := by
  obtain ⟨R,hR,hRK⟩ := hK.isBounded.exists_pos_norm_lt
  let b : ContDiffBump (0:ℂ) := ⟨R,R+1,hR,by linarith⟩
  let u (z : ℂ) := b z*‖z‖^2
  have hu : ContDiff ℝ 2 u := b.contDiff.mul (contDiff_id.norm_sq ℝ)
  have hs : HasCompactSupport u := b.hasCompactSupport.mul_right
  have he (z : ℂ) (hz : z∈K) : u =ᶠ[𝓝 z] (fun w => ‖w‖^2) := by
    have hb := b.eventuallyEq_one_of_mem_ball (show z∈ball (0:ℂ) b.rIn by
      simpa only [mem_ball_zero_iff] using hRK z hz)
    filter_upwards [hb] with w hw
    simp only [u,hw,Pi.one_apply,one_mul]
  exact ⟨u,hu,hs,he,fun z hz => (laplacian_congr_nhds (he z hz)).self_of_nhds.trans (complex_laplacian_norm_sq z)⟩

lemma hasCompactSupport_laplacian {u : ℂ → ℝ} (hs : HasCompactSupport u) :
    HasCompactSupport (Δ u) := by
  have h := (hs.fderiv ℝ |>.fderiv ℝ).comp_left
    (g := fun L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) => L 1 1+L Complex.I Complex.I) (by simp)
  simpa only [Function.comp_def,laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one] using h

lemma compact_quadratic_test_complement_integral
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ u : ℂ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      (∀ z∈K, u =ᶠ[𝓝 z] (fun w => ‖w‖^2)) ∧
      (∫ z in Kᶜ, (Δ u) z)≤0 := by
  obtain ⟨u,hu,hs,he,hΔ⟩ := exists_compact_quadratic_test K hK
  have hcont : Continuous (Δ u) := by
    exact continuous_iff_continuousAt.mpr (fun z => plane_laplacian_continuousAt (hu.contDiffAt (x := z)))
  have hsupport := hasCompactSupport_laplacian hs
  have hi : Integrable (Δ u) := hcont.integrable_of_hasCompactSupport hsupport
  have hzero := integral_laplacian_compact_eq_zero hu hs
  have hsum := integral_add_compl hK.measurableSet hi
  have hpos : 0≤∫ z in K, (Δ u) z := setIntegral_nonneg hK.measurableSet (fun z hz => by rw [hΔ z hz]; norm_num)
  refine ⟨u,hu,hs,he,?_⟩
  linarith

end SLEExactGauge

end

end OAI
