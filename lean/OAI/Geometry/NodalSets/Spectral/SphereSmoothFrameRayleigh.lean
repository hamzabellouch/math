import OAI.Geometry.NodalSets.Elliptic.FiniteLinearConstraints
import OAI.Geometry.NodalSets.Spectral.SphereResolventFormBounds

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Analysis
noncomputable section
local instance sphereFrameRayleighMeasurable : MeasurableSpace Base := borel Base
local instance sphereFrameRayleighBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_smooth_frame_rayleigh_upper (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu) (x : SphereEnergySmooth d)
    (hx : x ∈ Submodule.span ℝ (range u)) (hx0 : x ≠ 0) :
    sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
      (mu (Fin.last N))⁻¹-1 := by
  classical
  let J := sphereEnergyL2Linear d
  let C := sphereEnergyToCompletion d
  have hvar (i) (v : SphereEnergySmooth d) :
      inner ℝ (C (u i)) (C v) = (mu i)⁻¹ * inner ℝ (J (u i)) (J v) := by
    simpa only [C,J,sphereEnergyL2Map_coe] using
      sphere_resolvent_smooth_variational d (mu i) (hmu i).ne' (u i) (he i) (C v)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hcoef (i) : inner ℝ (J (u i)) (J x) = c i := by
    rw [← hc,map_sum]
    simp only [map_smul]
    exact ho.inner_right_fintype c i
  have hnorm : ‖J x‖^2 = ∑ i, c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hcoef,pow_two]
  have henergy : ‖C x‖^2 = ∑ i, (mu i)⁻¹*c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hvar,hcoef]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : ‖C x‖^2 ≤ (mu (Fin.last N))⁻¹*‖J x‖^2 := by
    rw [hnorm,henergy,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (hmu (Fin.last N)) (hanti (Fin.le_last i)))
      (sq_nonneg (c i))
  have hpos : 0 < ‖J x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (fun h ↦ hx0 ((sphereEnergyL2Linear_eq_zero_iff d x).mp h)))
  have hd : sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d x) (SphereEnergySmooth.toSmooth d x) =
      ‖C x‖^2-‖J x‖^2 := by
    rw [← sphereCompletedDirichlet_coe,sphereCompletedDirichlet,sphereEnergyL2Map_coe,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  rw [sphereRayleighQuotient,hd,← sphereEnergyL2Linear_norm_sq]
  exact (div_le_iff₀ hpos).mpr (by nlinarith [hb])

theorem sphere_smooth_frame_rayleigh_minmax (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    (∃ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
      ∀ x ∈ V, x ≠ 0 → sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
        (mu (Fin.last N))⁻¹-1) ∧
    (∀ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : SphereEnergySmooth d, x ∈ V ∧ x ≠ 0 ∧
        (mu (Fin.last N))⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x)) := by
  constructor
  · refine ⟨Submodule.span ℝ (range u),FiniteDimensional.span_of_finite ℝ (finite_range u),?_,?_⟩
    · have hli : LinearIndependent ℝ u := LinearIndependent.of_comp (sphereEnergyL2Linear d) ho.linearIndependent
      simpa using finrank_span_eq_card hli
    · exact sphere_smooth_frame_rayleigh_upper d u mu ho hmu he hanti
  · intro V hV hdim
    let := hV
    obtain ⟨x,hx,hx0,horth⟩ := subspace_nonzero_linear_constraints V (by omega)
      (fun i : Fin N ↦ (innerSL ℝ (sphereEnergyL2Linear d (u i.castSucc))).toLinearMap.comp (sphereEnergyL2Linear d))
    refine ⟨x,hx,hx0,sphere_smooth_rayleigh_of_resolvent_bound d _ (hmu _) x hx0 ?_⟩
    apply hmax
    intro j hj
    exact horth ⟨j.val,hj⟩

end
end Yau.Target

end OAI
