import OAI.Geometry.CylinderCovering.Singular.Cost

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace CylinderCovering.FlexibleSingular
open RuledApproximation

lemma hyperbolic_eventually {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ z ∈ labelDomain p c (ρ c) (q c),
      HyperbolicAt 1 (fun w => c • singularField p w) z ∧
      HyperbolicAt 1 (fun w => -c • singularField p w) z := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  have hlim : Tendsto (fun c : ℝ => C*(c*(ρ c)^(p-2))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hadm.2.2.1).const_mul C
  filter_upwards [self_mem_nhdsWithin,hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),hadm.1]
    with c hc hsmall hpos
  have hc : 0 < c := hc
  intro z hz
  have hd : 0 < ρ c := hpos.1
  have hz1 : 0 < z 1 := hd.trans_le hz.1
  have hb : |z 0| ≤ 2*z 1 := by linarith [hz.2.2.1]
  have hn := (hbound z hz1 hb).2
  have hr := Real.rpow_le_rpow_of_nonpos hd hz.1 (by linarith : p-2 ≤ 0)
  have hclt : c*‖fderiv ℝ (singularField p) z‖ < 1 := calc
    _ ≤ c*(C*(z 1)^(p-2)) := mul_le_mul_of_nonneg_left hn hc.le
    _ ≤ c*(C*(ρ c)^(p-2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr (by linarith)) hc.le
    _ = C*(c*(ρ c)^(p-2)) := by ring
    _ < 1 := hsmall
  exact ⟨singularField_scaled_hyperbolic hp hp2 hc.ne' hz1 hz.2.2.1
      (by simpa only [abs_of_pos hc] using hclt),
    singularField_scaled_hyperbolic hp hp2 (neg_ne_zero.mpr hc.ne') hz1 hz.2.2.1
      (by simpa only [abs_neg,abs_of_pos hc] using hclt)⟩

lemma scaled_smoothNear (p c q k : ℝ) {d : ℝ} (hd : 0 < d) :
    SmoothNear 1 (labelDomain p c d q) (fun z => k • singularField p z) := by
  obtain ⟨U,hU,hDU,hF⟩ := labelDomain_smoothNear p c q hd
  exact ⟨U,hU,hDU,(hF.of_le (by norm_num : (1:WithTop ℕ∞) ≤ ∞)).const_smul k⟩

lemma upperFamily_image (p c d q : ℝ) :
    (fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (labelDomain p c d q)
        (fun z => -c • singularField p z) 1) = upperFamily p c d q := by
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

theorem flexible_singular : Statement := by
  intro p ρ q hp hp' hadm
  have hs : (Real.sqrt 51)^2 = (51:ℝ) := Real.sq_sqrt (by norm_num)
  have hsn := Real.sqrt_nonneg (51:ℝ)
  have hs9 : Real.sqrt 51 < 9 := by nlinarith
  have hp2 : p < 2 := by linarith
  have hroot : 2*p+5 < Real.sqrt 51 := by linarith
  have hnum : 2*p^2+10*p-13 < 0 := by nlinarith
  have hk : singularCoefficient p < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum) (by linarith)
  refine ⟨hk,asymptotic hp hp2.le hadm,?_⟩
  filter_upwards [self_mem_nhdsWithin,geometric_cover hp hp2 hadm,
    hyperbolic_eventually hp hp2 hadm,totalCost_small hp hp2.le hadm hk,hadm.1]
    with c hc hgeom hhyp hcost hpos
  have hc : 0 < c := hc
  let eps : ℝ := (Real.sqrt 2/2-(2*cost p c (ρ c) (q c)+8*Real.sqrt 2*(ρ c)^2))/4
  have heps : 0 < eps := div_pos (sub_pos.mpr hcost) (by norm_num)
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hD := labelDomain_isCompact p c (ρ c) (q c)
  obtain ⟨n,C,hC,hcovC,hcostC⟩ := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (scaled_smoothNear p c (q c) c hpos.1) (fun z hz => (hhyp z hz).1) heps
  have hneg := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (scaled_smoothNear p c (q c) (-c) hpos.1) (fun z hz => (hhyp z hz).2) heps
  simp only [neg_smul,physicalWeight_neg] at hneg
  have hupper := (hneg.isometry swapReflect.toIsometryEquiv).isometry
    (IsometryEquiv.addLeft (vec3 0 0 (Real.sqrt 2)))
  simp only [← neg_smul] at hupper
  change HasFiniteCover Cylinder.parallelogram
    ((fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (labelDomain p c (ρ c) (q c))
        (fun z => -c • singularField p z) 1)) (cost p c (ρ c) (q c)+eps) at hupper
  rw [upperFamily_image] at hupper
  obtain ⟨m,D,hD,hcovD,hcostD⟩ := hupper
  refine ⟨n,m,C,D,lowerTipCylinder (ρ c),upperTipCylinder (ρ c),hC,hD,
    lowerTipCylinder_triangle (hpos.1),
    upperTipCylinder_triangle (hpos.1),hcovC,hcovD,
    lowerTipCylinder_carrier _,upperTipCylinder_carrier _,
    lowerTipCylinder_area hpos.1.le,upperTipCylinder_area hpos.1.le,?_,?_⟩
  · rw [lowerTipCylinder_carrier,upperTipCylinder_carrier]
    exact hgeom.trans (union_subset_union (union_subset_union (union_subset_union hcovC hcovD) Subset.rfl) Subset.rfl)
  · rw [lowerTipCylinder_area (hpos.1.le),
      upperTipCylinder_area (hpos.1.le)]
    change familyArea C ≤ cost p c (ρ c) (q c)+eps at hcostC
    dsimp only [eps] at hcostC hcostD
    linarith

end CylinderCovering.FlexibleSingular

end

end OAI
