import OAI.Geometry.NodalSets.Coefficients.CorrectionProductBounds
import OAI.Geometry.NodalSets.Elliptic.RoundPerturbationFlux

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma roundTensorPerturbation_seed_entry (a : Base → ℝ) (x : Yau.Jets.Coord) (j k : Fin 4) :
    intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv x) j k =
      if j=k then roundCoordFactor x*a (seedSphereFromCoord x) else 0 := by
  rw [roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp [Matrix.one_apply,seedSphereFromCoord,mul_comm]

theorem round_tensor_coordinate_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (alpha : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ alpha → tsupport alpha ⊆ Q →
      ∀ (a : Base → ℝ), (∀ x, a (seedSphereFromCoord x) = alpha x) →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i alpha x‖ ≤ eps) →
      ∀ x i j k, i ≤ J →
        ‖iteratedFDeriv ℝ i
          (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤
          C*eps := by
  obtain ⟨C,hC,hbound⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ J
  refine ⟨C,hC,?_⟩
  intro alpha hs hsup a ha eps heps hb x i j k hi
  have hprod (x : Yau.Jets.Coord) :
      ‖iteratedFDeriv ℝ i (fun y ↦ roundCoordFactor y*alpha y) x‖ ≤ C*eps := by
    by_cases hx : x ∈ Q
    · simpa using hbound alpha hs 1 eps (by norm_num) heps 0 x hx
        (fun l hl ↦ by simpa using hb x l hl) i hi
    · have hz : alpha =ᶠ[𝓝 x] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsup h))
      have hz' : (fun y ↦ roundCoordFactor y*alpha y) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
        filter_upwards [hz] with y hy
        simp [hy]
      rw [(hz'.iteratedFDeriv ℝ i).eq_of_nhds]
      simpa using mul_nonneg hC.le heps
  simp_rw [roundTensorPerturbation_seed_entry,ha]
  by_cases hj : j=k
  · simpa [hj] using hprod x
  · simp [hj]
    positivity

end
end Yau.Target

end OAI
