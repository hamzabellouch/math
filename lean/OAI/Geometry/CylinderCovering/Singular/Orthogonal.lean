import OAI.Geometry.CylinderCovering.Singular.Endpoint

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology
namespace CylinderCovering.FlexibleSingular
open RuledApproximation

lemma plane_graph_null {f : ℝ → ℝ} (hf : Continuous f) :
    volume {z : Plane | z 1 = f (z 0)} = 0 := by
  have hm : MeasurableSet {z : Plane | z 1 = f (z 0)} :=
    (isClosed_eq (by fun_prop) (hf.comp (by fun_prop))).measurableSet
  rw [← pairPlane_measurePreserving.measure_preimage hm.nullMeasurableSet,Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null (hm.preimage pairPlaneEquiv.measurable)
  filter_upwards [] with b
  have he : Prod.mk b ⁻¹' (pairPlaneEquiv ⁻¹' {z : Plane | z 1 = f (z 0)}) =
      {f b} := by
    ext r
    simp [pairPlaneEquiv_apply,vec2]
  rw [he]
  exact measure_singleton (f b)

lemma labelDomain_frontier_null (p c d q : ℝ) :
    volume (frontier (labelDomain p c d q)) = 0 := by
  have hb : Continuous (fun z : Plane => z 0) := by fun_prop
  have hr : Continuous (fun z : Plane => z 1) := by fun_prop
  have hcap : Continuous (fun b : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p b+q) := by
    unfold ceilingPolynomial
    fun_prop
  unfold labelDomain
  apply null_frontier_inter
  · apply measure_mono_null (frontier_le_subset_eq continuous_const hr)
    convert plane_graph_null (continuous_const : Continuous (fun _ : ℝ => d)) using 2
    ext z
    simp only [mem_ofPred_eq]
    exact eq_comm
  · apply null_frontier_inter
    · exact measure_mono_null (frontier_le_subset_eq hr continuous_const)
        (plane_graph_null (continuous_const : Continuous (fun _ : ℝ => (2:ℝ))))
    · apply null_frontier_inter
      · apply measure_mono_null (frontier_le_subset_eq hb.abs hr)
        convert plane_graph_null continuous_abs using 2
        ext z
        simp only [mem_ofPred_eq]
        exact eq_comm
      · exact measure_mono_null (frontier_le_subset_eq hr (hcap.comp hb))
          (plane_graph_null hcap)

lemma derivative_small_eventually {p : ℝ} {ρ q : ℝ → ℝ} (hp2 : p < 2)
    (hadm : SingularCutoff.Admissible p ρ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ z ∈ labelDomain p c (ρ c) (q c),
      ‖fderiv ℝ (fun w => c • singularField p w) z‖ < ε ∧
      ‖fderiv ℝ (fun w => -c • singularField p w) z‖ < ε := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  have hlim : Tendsto (fun c : ℝ => C*(c*(ρ c)^(p-2))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hadm.2.2.1).const_mul C
  filter_upwards [self_mem_nhdsWithin,hlim.eventually (gt_mem_nhds hε),hadm.1]
    with c hc hsmall hpos
  have hc : 0 < c := hc
  intro z hz
  have hd : 0 < ρ c := hpos.1
  have hz1 : 0 < z 1 := hd.trans_le hz.1
  have hb : |z 0| ≤ 2*z 1 := by linarith [hz.2.2.1]
  have hn := (hbound z hz1 hb).2
  have hr := Real.rpow_le_rpow_of_nonpos hd hz.1 (by linarith : p-2 ≤ 0)
  have hclt : c*‖fderiv ℝ (singularField p) z‖ < ε := calc
    _ ≤ c*(C*(z 1)^(p-2)) := mul_le_mul_of_nonneg_left hn hc.le
    _ ≤ c*(C*(ρ c)^(p-2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr (by linarith)) hc.le
    _ = C*(c*(ρ c)^(p-2)) := by ring
    _ < ε := hsmall
  have hdiff := (singularField_contDiffAt p hz1).differentiableAt (by norm_num)
  rw [fderiv_fun_const_smul hdiff,fderiv_fun_const_smul hdiff,
    norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,abs_of_pos hc]
  exact ⟨hclt,hclt⟩

lemma scaled_trace_det {p c : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hc : c ≠ 0) {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (fun w => c • singularField p w) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (fun w => c • singularField p w) z).toLinearMap < 0 := by
  have hdiff := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  have htd := singularField_hyperbolic hp hp2 hz hb
  rw [fderiv_fun_const_smul hdiff]
  constructor
  · change LinearMap.trace ℝ Plane (c • (fderiv ℝ (singularField p) z).toLinearMap) = 0
    simp [htd.1]
  · change LinearMap.det (c • (fderiv ℝ (singularField p) z).toLinearMap) < 0
    rw [LinearMap.det_smul]
    simpa using mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hc) htd.2

lemma orthogonal_families_eventually {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ e : ℝ, 0 < e →
      HasFiniteCover Cylinder.parallelogram (lowerFamily p c (ρ c) (q c))
        (cost p c (ρ c) (q c)+e) ∧
      HasFiniteCover Cylinder.parallelogram (upperFamily p c (ρ c) (q c))
        (cost p c (ρ c) (q c)+e) := by
  filter_upwards [self_mem_nhdsWithin,
    derivative_small_eventually hp2 hadm (by norm_num : (0:ℝ)<1/2),hadm.1]
    with c hc hnorm hpos
  have hc : 0 < c := hc
  have hhyp : ∀ z ∈ labelDomain p c (ρ c) (q c),
      LinearMap.trace ℝ Plane (fderiv ℝ (fun w => c • singularField p w) z).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ (fun w => c • singularField p w) z).toLinearMap < 0 ∧
      ‖fderiv ℝ (fun w => c • singularField p w) z‖ ≤ 1/2 := by
    intro z hz
    have ht := scaled_trace_det hp hp2 hc.ne' (hpos.1.trans_le hz.1) hz.2.2.1
    exact ⟨ht.1,ht.2,(hnorm z hz).1.le⟩
  have hhypNeg : ∀ z ∈ labelDomain p c (ρ c) (q c),
      LinearMap.trace ℝ Plane (fderiv ℝ (fun w => -c • singularField p w) z).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ (fun w => -c • singularField p w) z).toLinearMap < 0 ∧
      ‖fderiv ℝ (fun w => -c • singularField p w) z‖ ≤ 1/2 := by
    intro z hz
    have ht := scaled_trace_det hp hp2 (neg_ne_zero.mpr hc.ne')
      (hpos.1.trans_le hz.1) hz.2.2.1
    exact ⟨ht.1,ht.2,(hnorm z hz).2.le⟩
  intro e he
  have hlow := orthogonalGrid (labelDomain p c (ρ c) (q c))
    (fun w => c • singularField p w) (1/2)
    (labelDomain_isCompact _ _ _ _) (labelDomain_frontier_null _ _ _ _)
    (scaled_smoothNear p c (q c) c hpos.1) (by norm_num) hhyp e he
  have hneg := orthogonalGrid (labelDomain p c (ρ c) (q c))
    (fun w => -c • singularField p w) (1/2)
    (labelDomain_isCompact _ _ _ _) (labelDomain_frontier_null _ _ _ _)
    (scaled_smoothNear p c (q c) (-c) hpos.1) (by norm_num) hhypNeg e he
  have hlow' : HasFiniteCover Cylinder.parallelogram
      (lowerFamily p c (ρ c) (q c)) (cost p c (ρ c) (q c)+e) := by
    simpa only [lowerFamily,cost,physicalWeight,
      Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)] using hlow
  have hneg' : HasFiniteCover Cylinder.parallelogram
      (physicalRuled (Real.sqrt 2) (labelDomain p c (ρ c) (q c))
        (fun w => -c • singularField p w) 1) (cost p c (ρ c) (q c)+e) := by
    simpa only [cost,physicalWeight,Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),
      neg_smul,PiLp.neg_apply,neg_sq] using hneg
  have hu := (hneg'.isometry swapReflect.toIsometryEquiv).isometry
    (IsometryEquiv.addLeft (vec3 0 0 (Real.sqrt 2)))
  change HasFiniteCover Cylinder.parallelogram
    ((fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (labelDomain p c (ρ c) (q c))
        (fun w => -c • singularField p w) 1)) (cost p c (ρ c) (q c)+e) at hu
  rw [upperFamily_image] at hu
  exact ⟨hlow',hu⟩

theorem orthogonal_statement : OrthogonalStatement := by
  intro p ρ q hp hp2 hadm
  exact ⟨fun c => labelDomain_frontier_null p c (ρ c) (q c),
    fun e he => derivative_small_eventually hp2 hadm he,
    orthogonal_families_eventually hp hp2 hadm⟩

end CylinderCovering.FlexibleSingular

end

end OAI
