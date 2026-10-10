import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra
import OAI.Analysis.CircleDomains.Sobolev.CompactWeakDerivativeIntegral

namespace OAI

/-! Quantitative global energy for a compact cutoff of a local Sobolev
error. This applies to the flattened height minus the vertical coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_cutoff_energy_bound {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u η : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u U)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) (hsub : tsupport η ⊆ U)
    {C₀ C₁ e : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (he : 0 ≤ e)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hub : ∀ x ∈ U, |u x| ≤ e) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => η x*u x) univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤
        2*C₀^2*(∫ x in U, ‖W.weakGrad x‖^2)+4*C₁^2*e^2*(volume U).toReal := by
  let J := W.mul_smooth_bounded_p (by norm_num) hU hη hC₀ hC₁ hηb hηd
  obtain ⟨V⟩ := exists_global_compact_cutoff_witness hU W.memW1p hη hs hsub
  have hVG := (V.restrict hU (subset_univ U)).ae_eq hU J
  change V.weakGrad =ᵐ[volume.restrict U] J.weakGrad at hVG
  have hparts (x : EuclideanPlane) (i : Fin 2) :
      J.weakGrad x i = η x*W.weakGrad x i+fderiv ℝ η x (EuclideanSpace.single i 1)*u x := by
    simp only [J, DeGiorgi.MemW1pWitness.mul_smooth_bounded_p, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
  have hd (x : EuclideanPlane) (i : Fin 2) :
      |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ C₁ := by
    have hh := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i 1)
    have hh' : |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ ‖fderiv ℝ η x‖ := by
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using hh
    exact hh'.trans (hηd x)
  have hbound : ∀ x ∈ U, ‖J.weakGrad x‖^2 ≤
      2*C₀^2*‖W.weakGrad x‖^2+4*C₁^2*e^2 := by
    intro x hx
    rw [plane_norm_sq, hparts x 0, hparts x 1, plane_norm_sq]
    exact cutoff_gradient_square_bound hC₀ hC₁ he (hηb x) (hub x hx) (hd x 0) (hd x 1)
  have hz : ∀ᵐ x ∂volume, x ∉ U → ‖V.weakGrad x‖^2 = 0 := by
    filter_upwards [compact_weakGradient_zero_off V 0, compact_weakGradient_zero_off V 1] with x h0 h1 hx
    have hx' : x ∉ tsupport (fun x => η x*u x) := fun h => hx (hsub (tsupport_mul_subset_left h))
    rw [plane_norm_sq, h0 hx', h1 hx']
    norm_num
  have hJi := J.weakGrad_norm_memLp.integrable_sq
  have hWi := W.weakGrad_norm_memLp.integrable_sq
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUf
  have hci : Integrable (fun _ : EuclideanPlane => 4*C₁^2*e^2) (volume.restrict U) := integrable_const _
  refine ⟨V, ?_⟩
  calc
    _ = ∫ x in U, ‖V.weakGrad x‖^2 := (setIntegral_eq_integral_of_ae_compl_eq_zero hz).symm
    _ = ∫ x in U, ‖J.weakGrad x‖^2 := integral_congr_ae (hVG.mono (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))
    _ ≤ ∫ x in U, 2*C₀^2*‖W.weakGrad x‖^2+4*C₁^2*e^2 :=
      integral_mono_ae hJi ((hWi.const_mul _).add hci)
        ((ae_restrict_mem hU.measurableSet).mono fun x hx => hbound x hx)
    _ = _ := by
      rw [integral_add (hWi.const_mul _) hci, integral_const_mul, integral_const]
      simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul]
      ring

end CircleDomainRigidity

end

end OAI
