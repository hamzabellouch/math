import OAI.Geometry.RuledCovering.SingularGeometry
import OAI.Geometry.RuledCovering.SingularAsymptotics
import OAI.Geometry.RuledCovering.TipCylinders

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_hyperbolic_eventually {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ z ∈ singularDomain p gamma c,
      HyperbolicAt 1 (fun w => c • singularField p w) z ∧
      HyperbolicAt 1 (fun w => -c • singularField p w) z := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  have hlim : Tendsto (fun c : ℝ => C*(c*(c^gamma)^(p-2))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (singular_cutoff_small hpg).const_mul C
  filter_upwards [self_mem_nhdsWithin,hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with c hc hsmall
  have hc : 0 < c := hc
  intro z hz
  have hd : 0 < c^gamma := Real.rpow_pos_of_pos hc gamma
  have hz1 : 0 < z 1 := hd.trans_le hz.1
  have hb : |z 0| ≤ 2*z 1 := by linarith [hz.2.2.1]
  have hn := (hbound z hz1 hb).2
  have hr := Real.rpow_le_rpow_of_nonpos hd hz.1 (by linarith : p-2 ≤ 0)
  have hclt : c*‖fderiv ℝ (singularField p) z‖ < 1 := calc
    _ ≤ c*(C*(z 1)^(p-2)) := mul_le_mul_of_nonneg_left hn hc.le
    _ ≤ c*(C*(c^gamma)^(p-2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr (by linarith)) hc.le
    _ = C*(c*(c^gamma)^(p-2)) := by ring
    _ < 1 := hsmall
  exact ⟨singularField_scaled_hyperbolic hp hp2 hc.ne' hz1 hz.2.2.1
      (by simpa only [abs_of_pos hc] using hclt),
    singularField_scaled_hyperbolic hp hp2 (neg_ne_zero.mpr hc.ne') hz1 hz.2.2.1
      (by simpa only [abs_neg,abs_of_pos hc] using hclt)⟩

lemma singular_scaled_smoothNear (p gamma k : ℝ) {c : ℝ} (hc : 0 < c) :
    SmoothNear 1 (singularDomain p gamma c) (fun z => k • singularField p z) := by
  obtain ⟨U,hU,hDU,hF⟩ := singularDomain_smoothNear p gamma hc
  exact ⟨U,hU,hDU,(hF.of_le (by norm_num : (1:WithTop ℕ∞) ≤ ∞)).const_smul k⟩

lemma physicalWeight_neg (h : ℝ) (g : Plane) : physicalWeight h (-g) = physicalWeight h g := by
  simp [physicalWeight]

lemma singularUpper_image (p gamma c : ℝ) :
    (fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
        (fun z => -c • singularField p z) 1) = singularUpper p gamma c := by
  ext z
  constructor
  · rintro ⟨_,⟨_,⟨b,hb,s,hs,rfl⟩,rfl⟩,rfl⟩
    refine ⟨b,hb,s,hs,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3] <;> ring
  · rintro ⟨b,hb,s,hs,rfl⟩
    refine ⟨swapReflect (vec3 s (b 0+s*(-c • singularField p b) 0)
      (Real.sqrt 2*(b 1+s*(-c • singularField p b) 1))),
      ⟨_,⟨b,hb,s,hs,rfl⟩,rfl⟩,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3] <;> ring

/-- Singular-field approximation. The positive parameter is fixed before
choosing either finite approximation, and both errors use its strict saving. -/
theorem singular : SingularStatement := by
  intro p gamma hp hp' hg hg'
  obtain ⟨hp2,hpg,_,hk⟩ := singular_parameter_bounds hp hp' hg hg'
  refine ⟨hk,singular_asymptotic hp hp2.le hg,?_⟩
  filter_upwards [self_mem_nhdsWithin,singular_geometric_cover hp hp2 hpg,
    singular_hyperbolic_eventually hp hp2 hpg,singular_totalCost_small hp hp2.le hg hk]
    with c hc hgeom hhyp hcost
  have hc : 0 < c := hc
  let eps : ℝ := (Real.sqrt 2/2-(2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2))/4
  have heps : 0 < eps := div_pos (sub_pos.mpr hcost) (by norm_num)
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hD := singularDomain_isCompact p gamma c
  obtain ⟨n,C,hC,hcovC,hcostC⟩ := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (singular_scaled_smoothNear p gamma c hc) (fun z hz => (hhyp z hz).1) heps
  have hneg := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (singular_scaled_smoothNear p gamma (-c) hc) (fun z hz => (hhyp z hz).2) heps
  simp only [neg_smul,physicalWeight_neg] at hneg
  have hupper := (hneg.isometry swapReflect.toIsometryEquiv).isometry
    (IsometryEquiv.addLeft (vec3 0 0 (Real.sqrt 2)))
  simp only [← neg_smul] at hupper
  change HasFiniteCover Cylinder.parallelogram
    ((fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
        (fun z => -c • singularField p z) 1)) (singularCost p gamma c+eps) at hupper
  rw [singularUpper_image] at hupper
  obtain ⟨m,D,hD,hcovD,hcostD⟩ := hupper
  refine ⟨n,m,C,D,lowerTipCylinder (c^gamma),upperTipCylinder (c^gamma),hC,hD,
    lowerTipCylinder_triangle (Real.rpow_pos_of_pos hc gamma),
    upperTipCylinder_triangle (Real.rpow_pos_of_pos hc gamma),hcovC,hcovD,
    lowerTipCylinder_carrier _,upperTipCylinder_carrier _,?_,?_⟩
  · rw [lowerTipCylinder_carrier,upperTipCylinder_carrier]
    exact hgeom.trans (union_subset_union (union_subset_union (union_subset_union hcovC hcovD) Subset.rfl) Subset.rfl)
  · rw [lowerTipCylinder_area (Real.rpow_nonneg hc.le gamma),
      upperTipCylinder_area (Real.rpow_nonneg hc.le gamma)]
    change familyArea C ≤ singularCost p gamma c+eps at hcostC
    dsimp only [eps] at hcostC hcostD
    linarith

end RuledApproximation

end

end OAI
