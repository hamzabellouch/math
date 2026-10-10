import OAI.Probability.SLE.Geometry.RootExteriorChart

namespace OAI

/-! The exterior map has compact omitted set. This supplies the compact
region used in the area proof of the second-coefficient estimate. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_image_isOpen {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hi : InjOn f D) : IsOpen (f '' D) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z,hz,rfl⟩
  apply univalent_nhds_le_map hD hf hi hz
  exact image_mem_map (hD.mem_nhds hz)

lemma root_exterior_contains_far_points {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1)) :
    ∃ R : ℝ, 0<R ∧ ∀ w : ℂ, R<‖w‖ →
      w∈rootExteriorChart q '' {z : ℂ | 1<‖z‖} := by
  let H (z : ℂ) := z*q (z^2)
  have hs (z : ℂ) (hz : z∈ball (0:ℂ) 1) : z^2∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz) (by norm_num)
  have hH : DifferentiableOn ℂ H (ball 0 1) :=
    differentiableOn_id.mul (hq.comp (differentiable_id.pow 2).differentiableOn hs)
  have hH0 : H 0=0 := by simp [H]
  have hnhds : H '' ball (0:ℂ) 1∈𝓝 0 := by
    simpa only [hH0] using (univalent_image_isOpen isOpen_ball hH hi).mem_nhds
      (mem_image_of_mem H (mem_ball_self zero_lt_one))
  obtain ⟨ε,hε,hεH⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨max 1 ε⁻¹,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro w hw
  have hw0 : w≠0 := norm_ne_zero_iff.mp (ne_of_gt ((lt_of_lt_of_le zero_lt_one (le_max_left _ _)).trans hw))
  have hwi : w⁻¹∈ball (0:ℂ) ε := by
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hw0) hε).mpr ((le_max_right _ _).trans_lt hw)
  obtain ⟨z,hz,hzw⟩ := hεH hwi
  have hz0 : z≠0 := by intro he; rw [he,hH0] at hzw; exact (inv_ne_zero hw0) hzw.symm
  refine ⟨z⁻¹,?_,?_⟩
  · change 1<‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz)
  · apply inv_injective
    simpa [rootExteriorChart,H,div_eq_mul_inv,mul_comm] using hzw

lemma root_exterior_omitted_isCompact {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1)) :
    IsCompact (rootExteriorChart q '' {z : ℂ | 1<‖z‖})ᶜ := by
  have hD : IsOpen {z : ℂ | 1<‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨hf,hfI⟩ := root_exterior_univalent hq hne hi
  have hc : IsClosed (rootExteriorChart q '' {z : ℂ | 1<‖z‖})ᶜ :=
    (univalent_image_isOpen hD hf hfI).isClosed_compl
  obtain ⟨R,_,hR⟩ := root_exterior_contains_far_points hq hi
  have hb : (rootExteriorChart q '' {z : ℂ | 1<‖z‖})ᶜ⊆closedBall (0:ℂ) R := by
    intro z hz
    rw [mem_closedBall,dist_zero_right]
    exact le_of_not_gt (fun h => hz (hR z h))
  exact (isCompact_closedBall (0:ℂ) R).of_isClosed_subset hc hb

end SLEExactGauge

end

end OAI
