import OAI.Probability.SLE.Geometry.RootExteriorCompact

namespace OAI

/-! Compact omitted sets for every circle strictly outside the unit disk. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma root_exterior_contains_far_points_radius {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1))
    {r : ℝ} (hr : 1<r) :
    ∃ R : ℝ, 0<R ∧ ∀ w : ℂ, R<‖w‖ →
      w∈rootExteriorChart q '' {z : ℂ | r<‖z‖} := by
  let H (z : ℂ) := z*q (z^2)
  have hr0 : 0<r := zero_lt_one.trans hr
  have hri : 0<r⁻¹ := inv_pos.mpr hr0
  have hri1 : r⁻¹<1 := inv_lt_one_of_one_lt₀ hr
  have hsub : ball (0:ℂ) r⁻¹ ⊆ ball 0 1 := ball_subset_ball hri1.le
  have hs (z : ℂ) (hz : z∈ball (0:ℂ) r⁻¹) : z^2∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp (hsub hz)) (by norm_num)
  have hH : DifferentiableOn ℂ H (ball 0 r⁻¹) :=
    differentiableOn_id.mul (hq.comp (differentiable_id.pow 2).differentiableOn hs)
  have hH0 : H 0=0 := by simp [H]
  have hnhds : H '' ball (0:ℂ) r⁻¹∈𝓝 0 := by
    simpa only [hH0] using (univalent_image_isOpen isOpen_ball hH (hi.mono hsub)).mem_nhds
      (mem_image_of_mem H (mem_ball_self hri))
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
  · change r<‖z⁻¹‖
    rw [norm_inv]
    exact (lt_inv_comm₀ hr0 (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz)
  · apply inv_injective
    simpa [rootExteriorChart,H,div_eq_mul_inv,mul_comm] using hzw

lemma root_exterior_omitted_radius_isCompact {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1))
    {r : ℝ} (hr : 1<r) :
    IsCompact (rootExteriorChart q '' {z : ℂ | r<‖z‖})ᶜ := by
  have hD : IsOpen {z : ℂ | r<‖z‖} := isOpen_lt continuous_const continuous_norm
  have hsub : {z : ℂ | r<‖z‖} ⊆ {z : ℂ | 1<‖z‖} := fun z hz => hr.trans hz
  obtain ⟨hf,hfI⟩ := root_exterior_univalent hq hne hi
  have hc : IsClosed (rootExteriorChart q '' {z : ℂ | r<‖z‖})ᶜ :=
    (univalent_image_isOpen hD (hf.mono hsub) (hfI.mono hsub)).isClosed_compl
  obtain ⟨R,_,hR⟩ := root_exterior_contains_far_points_radius hq hi hr
  have hb : (rootExteriorChart q '' {z : ℂ | r<‖z‖})ᶜ⊆closedBall (0:ℂ) R := by
    intro z hz
    rw [mem_closedBall,dist_zero_right]
    exact le_of_not_gt (fun h => hz (hR z h))
  exact (isCompact_closedBall (0:ℂ) R).of_isClosed_subset hc hb

lemma root_exterior_circle_omitted {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1))
    {r : ℝ} (hr : 1<r) {z : ℂ} (hz : ‖z‖=r) :
    rootExteriorChart q z ∈ (rootExteriorChart q '' {w : ℂ | r<‖w‖})ᶜ := by
  rintro ⟨w,hw,he⟩
  have hzw := (root_exterior_univalent hq hne hi).2 (hr.trans hw)
    (by change 1<‖z‖; rw [hz]; exact hr) he
  subst w
  exact lt_irrefl r (hz ▸ hw)

lemma root_exterior_tendsto_cocompact {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0) :
    Tendsto (rootExteriorChart q) (cocompact ℂ) (cocompact ℂ) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hpow : Tendsto (fun z : ℂ => z⁻¹^2) (cocompact ℂ) (𝓝 0) := by simpa using hinv.pow 2
  have hqcont := (hq.differentiableAt (ball_mem_nhds (0:ℂ) zero_lt_one)).continuousAt
  have hlim : Tendsto (fun z : ℂ => (rootExteriorChart q z)⁻¹)
      (cocompact ℂ) (𝓝 0) := by
    have hh := hinv.mul (hqcont.tendsto.comp hpow)
    simp only [rootExteriorChart,inv_div]
    simpa only [div_eq_mul_inv,mul_comm,zero_mul,Function.comp_def] using hh
  have hne' : ∀ᶠ z in cocompact ℂ, (rootExteriorChart q z)⁻¹≠0 := by
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact,
      hpow (ball_mem_nhds (0:ℂ) zero_lt_one)] with z hz hqz
    exact inv_ne_zero (div_ne_zero hz (hne _ hqz))
  have ht : Tendsto (fun z : ℂ => (rootExteriorChart q z)⁻¹)
      (cocompact ℂ) (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hlim,hne'⟩
  have hh := tendsto_inv₀_nhdsNE_zero.comp ht
  simpa only [Function.comp_def,inv_inv,Metric.cobounded_eq_cocompact] using hh

end SLEExactGauge

end

end OAI
