import Mathlib.Analysis.InnerProductSpace.Spectrum
import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereResolventSpectrumMeasurable : MeasurableSpace Base := borel Base
local instance sphereResolventSpectrumBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereL2Resolvent_eigenvalue_bounds (d : SphereEnergyData) (mu : ℝ) (f : SphereWeightedL2 d)
    (hf : f ≠ 0) (he : sphereL2Resolvent d f = mu • f) : 0 < mu ∧ mu ≤ 1 := by
  have hpos := sphereL2Resolvent_positive d f hf
  rw [he,inner_smul_left_eq_smul,real_inner_self_eq_norm_sq,smul_eq_mul] at hpos
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hm : 0 < mu := (mul_pos_iff_of_pos_right (sq_pos_of_pos hn)).mp hpos
  refine ⟨hm,?_⟩
  have h := (sphereL2Resolvent d).le_opNorm f
  have hb := mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hm] at h
  nlinarith

theorem sphereL2Resolvent_eigenspace_finite (d : SphereEnergyData) (mu : ℝ) (hmu : mu ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (sphereL2Resolvent d).toLinearMap mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (sphereL2Resolvent_compact d) mu hmu

theorem sphereL2Resolvent_eigenspaces_total (d : SphereEnergyData) :
    (⨆ mu : ℝ, Module.End.eigenspace (sphereL2Resolvent d).toLinearMap mu).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (sphereL2Resolvent_compact d) (sphereL2Resolvent_symmetric d)

theorem sphereL2Resolvent_eigenfunction_weak (d : SphereEnergyData) (mu : ℝ) (f : SphereWeightedL2 d)
    (hf : f ≠ 0) (he : sphereL2Resolvent d f = mu • f) :
    sphereEnergyL2Map d (sphereWeakSolution d f) ≠ 0 ∧ 0 ≤ mu⁻¹-1 ∧
    ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereWeakSolution d f) v =
        (mu⁻¹-1)*inner ℝ (sphereEnergyL2Map d (sphereWeakSolution d f)) (sphereEnergyL2Map d v) := by
  obtain ⟨hm,hmu⟩ := sphereL2Resolvent_eigenvalue_bounds d mu f hf he
  have hJ : sphereEnergyL2Map d (sphereWeakSolution d f) = mu • f := he
  refine ⟨?_,?_,?_⟩
  · rw [hJ]
    exact smul_ne_zero hm.ne' hf
  · have h : 1 ≤ mu⁻¹ := (one_le_inv₀ hm).mpr hmu
    linarith
  · intro v
    rw [sphereCompletedDirichlet,sphereWeakSolution_spec,hJ,inner_smul_left_eq_smul,smul_eq_mul]
    field_simp

end
end Yau.Target

end OAI
