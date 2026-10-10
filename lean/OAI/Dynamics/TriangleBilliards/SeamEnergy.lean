import OAI.Dynamics.TriangleBilliards.TransverseFlow

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped NNReal ContDiff

/-- Global equal Cauchy--Riemann norms on the genuine smooth seam core.
The integration-by-parts step is supplied by the actual measure-preserving
geodesic/transverse generators and the proved pointwise Schwarz identity. -/
lemma seam_CR_norms {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C Cx Cy : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hCx : ∀ x v b, ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ Cx)
    (hCy : ∀ x v b, ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ Cy)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hxf : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hyf : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (hxyf : MemLp (xDerivative (yDerivative f)) 2 (doubleMeasure Q)) :
    ‖hxf.toLp (xDerivative f) + Complex.I • hyf.toLp (yDerivative f)‖ =
      ‖hxf.toLp (xDerivative f) - Complex.I • hyf.toLp (yDerivative f)‖ := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have he : xDerivative (yDerivative f) = yDerivative (xDerivative f) := funext (x_y_commute hd)
  have hyxf : MemLp (yDerivative (xDerivative f)) 2 (doubleMeasure Q) := by
    rwa [← he]
  have h₁ := seam_geodesic_generator hs hd' hC hf hxf
  have h₂ := seam_transverse_generator hs hd' hC hf hyf
  have h₃ := seam_geodesic_generator (hs.yDerivative hd')
    (fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)) hCy hyf hxyf
  have h₄ := seam_transverse_generator (hs.xDerivative hd')
    (fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)) hCx hxf hyxf
  have heLp : hxyf.toLp (xDerivative (yDerivative f)) = hyxf.toLp (yDerivative (xDerivative f)) :=
    MemLp.toLp_congr hxyf hyxf (Filter.Eventually.of_forall (congrFun he))
  rw [← heLp] at h₄
  exact HilbertFlow.commuting_generators_CR h₁ h₂ h₃ h₄

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology ContDiff

lemma raw_eq_one_of_norm_le {x : ℂ} (hx : ‖x‖ ≤ (1/2 : ℝ)) : raw x = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num)
  rw [norm_smul, Real.norm_ofNat]
  linarith

lemma raw_eq_zero_of_one_le_norm {x : ℂ} (hx : 1 ≤ ‖x‖) : raw x = 0 := by
  have h : x ∉ Function.support raw := by
    rw [raw_support, mem_ball_zero_iff]
    exact not_lt.mpr hx
  exact Function.notMem_support.mp h

/-- An explicit vertex cutoff, zero up to radius R and one outside radius
2R. Its transition annuli are those used in the localized energy bound. -/
def vertexCutoffFactor (Q : Triangle) (R : ℝ) (i : Fin 3) (x : ℂ) : ℝ :=
  1 - raw ((2 * R)⁻¹ • (x - Q.vertex i))

def vertexCutoff (Q : Triangle) (R : ℝ) (x : ℂ) : ℝ :=
  ∏ i : Fin 3, vertexCutoffFactor Q R i x

lemma vertexCutoffFactor_mem_Icc (Q : Triangle) (R : ℝ) (i : Fin 3) (x : ℂ) :
    vertexCutoffFactor Q R i x ∈ Icc (0 : ℝ) 1 := by
  exact ⟨sub_nonneg.mpr (raw_le_one _), sub_le_self _ (raw_nonneg _)⟩

lemma vertexCutoff_mem_Icc (Q : Triangle) (R : ℝ) (x : ℂ) :
    vertexCutoff Q R x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).1)
  · exact Finset.prod_le_one₀ (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).1)
      (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).2)

lemma vertexCutoffFactor_zero (Q : Triangle) {R : ℝ} (hR : 0 < R) (i : Fin 3) {x : ℂ}
    (hx : ‖x - Q.vertex i‖ ≤ R) : vertexCutoffFactor Q R i x = 0 := by
  unfold vertexCutoffFactor
  rw [raw_eq_one_of_norm_le, sub_self]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
  calc
    (2 * R)⁻¹ * ‖x - Q.vertex i‖ ≤ (2 * R)⁻¹ * R := by gcongr
    _ = 1 / 2 := by field_simp

lemma vertexCutoffFactor_one (Q : Triangle) {R : ℝ} (hR : 0 < R) (i : Fin 3) {x : ℂ}
    (hx : 2 * R ≤ ‖x - Q.vertex i‖) : vertexCutoffFactor Q R i x = 1 := by
  unfold vertexCutoffFactor
  rw [raw_eq_zero_of_one_le_norm, sub_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
  calc
    1 = (2 * R)⁻¹ * (2 * R) := (inv_mul_cancel₀ (mul_ne_zero (by norm_num) hR.ne')).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (mul_nonneg (by norm_num) hR.le))

lemma vertexCutoff_zero (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : Q.clearance x ≤ R) : vertexCutoff Q R x = 0 := by
  obtain ⟨v, hv, hd⟩ := (Set.finite_range Q.vertex).isCompact.exists_infDist_eq_dist
    (Set.range_nonempty Q.vertex) x
  obtain ⟨i, rfl⟩ := hv
  have hi : ‖x - Q.vertex i‖ ≤ R := by
    change Metric.infDist x (range Q.vertex) ≤ R at hx
    rw [hd, dist_eq_norm] at hx
    exact hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (vertexCutoffFactor_zero Q hR i hi)

lemma vertexCutoff_one (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : 2 * R ≤ Q.clearance x) : vertexCutoff Q R x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply vertexCutoffFactor_one Q hR i
  exact hx.trans (by
    simpa only [Triangle.clearance, dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (x := x) (s := range Q.vertex) (Set.mem_range_self i) : Q.clearance x ≤ ‖x - Q.vertex i‖)

lemma vertexCutoffFactor_contDiff (Q : Triangle) (R : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (vertexCutoffFactor Q R i) := by
  unfold vertexCutoffFactor
  have h : ContDiff ℝ ∞ (fun x : ℂ => (2 * R)⁻¹ • (x - Q.vertex i)) := by fun_prop
  exact contDiff_const.sub (raw_contDiff.comp h)

lemma vertexCutoff_contDiff (Q : Triangle) (R : ℝ) : ContDiff ℝ ∞ (vertexCutoff Q R) := by
  exact contDiff_prod (fun i _ => vertexCutoffFactor_contDiff Q R i)

lemma reflected_vertex_dist (Q : Triangle) (i k : Fin 3) (hk : k = i ∨ k = i+1) (x : ℂ) :
    ‖wallReflection Q i x - Q.vertex k‖ = ‖x - Q.vertex k‖ := by
  have hfix : wallReflection Q i (Q.vertex k) = Q.vertex k := by
    rcases hk with rfl | rfl
    · simp [wallReflection, reflect]
    · unfold wallReflection
      change Q.vertex i + reflect (Q.tangent i) (Q.tangent i) = _
      rw [reflect_tangent (Q.tangent_ne_zero i)]
      simp [Triangle.tangent]
  calc
    _ = ‖wallReflection Q i x - wallReflection Q i (Q.vertex k)‖ := by rw [hfix]
    _ = _ := by rw [wallReflection_sub, reflect_norm (Q.tangent_ne_zero i)]

lemma side_opposite_dist_lower (Q : Triangle) (i : Fin 3) {x : ℂ} (hx : x ∈ Q.side i) :
    1 ≤ Q.coordinateBound * ‖x - Q.vertex (i+2)‖ := by
  have h := Q.coord_norm_le (i+2) x (Q.vertex (i+2))
  have hz : Q.basis.coord (i+2) x = 0 := (Q.side_coord_zero_iff hx _).mpr rfl
  rw [hz] at h
  have h1 : Q.basis.coord (i+2) (Q.vertex (i+2)) = 1 := Q.basis.coord_apply_eq (i+2)
  rw [h1] at h
  simpa only [zero_sub, abs_neg, abs_one] using h

/-- Scale condition only on geometric constants of the fixed nondegenerate
triangle. It imposes no Diophantine angle condition. -/
lemma vertexCutoff_seam_germ (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (i : Fin 3) {x : ℂ} (hx : x ∈ Q.side i) :
    ∀ᶠ y in 𝓝 x, vertexCutoff Q R (wallReflection Q i y) = vertexCutoff Q R y := by
  have hfar : 2 * R < ‖x - Q.vertex (i+2)‖ := by
    by_contra hn
    have hn := le_of_not_gt hn
    have hb := side_opposite_dist_lower Q i hx
    nlinarith [Q.coordinateBound_nonneg]
  have hc : Continuous (fun y : ℂ => ‖y - Q.vertex (i+2)‖) := by fun_prop
  have hr : Continuous (fun y : ℂ => ‖wallReflection Q i y - Q.vertex (i+2)‖) :=
    hc.comp (wallReflection_contDiff Q i).continuous
  have hfar' : 2 * R < ‖wallReflection Q i x - Q.vertex (i+2)‖ := by
    rwa [wallReflection_fixed_side Q hx]
  filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds hfar),
    hr.continuousAt.eventually (Ioi_mem_nhds hfar')] with y hy hry
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k = i+2
  · subst k
    rw [vertexCutoffFactor_one Q hR _ hry.le, vertexCutoffFactor_one Q hR _ hy.le]
  · have hk' : k = i ∨ k = i+1 := by
      have hfin : ∀ i k : Fin 3, k ≠ i+2 → k = i ∨ k = i+1 := by decide
      exact hfin i k hk
    unfold vertexCutoffFactor
    congr 1
    apply raw_radial
    simp only [norm_smul, reflected_vertex_dist Q i k hk']

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology ContDiff

/-- The supported smoothing used for bounded-mode regularity. -/
def supportedSmoothing (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ) : DoublePhase → ℂ :=
  fun z => vertexCutoff Q R z.1.1 • reflectedSmoothing Q ε f z

lemma supportedSmoothing_zero {Q : Triangle} {ε R : ℝ} (hR : 0 < R)
    (f : DoublePhase → ℂ) (z : DoublePhase) (hz : Q.clearance z.1.1 ≤ R) :
    supportedSmoothing Q ε R f z = 0 := by
  simp only [supportedSmoothing, vertexCutoff_zero Q hR hz, zero_smul]

lemma supportedSmoothing_seam (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    (hR : Q.safetyFactor * ε < R) (hsmall : 2 * R * Q.coordinateBound < 1)
    (f : DoublePhase → ℂ) : SeamCompatible Q (supportedSmoothing Q ε R f) := by
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  intro i x hx v b
  by_cases hs : Q.safetyFactor * ε < Q.clearance x
  · filter_upwards [vertexCutoff_seam_germ Q hRp hsmall i hx,
      reflectedSmoothing_seam_germ Q hx hε hs f b v] with y hy hyy
    simp only [supportedSmoothing, hy, hyy]
  · have hxr : Q.clearance x < R := (le_of_not_gt hs).trans_lt hR
    have hc := Q.clearance_lipschitz.continuous
    have hxr' : Q.clearance (wallReflection Q i x) < R := by
      rwa [wallReflection_fixed_side Q hx]
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hxr),
      (hc.comp (wallReflection_contDiff Q i).continuous).continuousAt.eventually
        (Iio_mem_nhds hxr')] with y hy hry
    exact (supportedSmoothing_zero (ε := ε) hRp f
      ((wallReflection Q i y, reflectedDirection Q i v),b+1) hry.le).trans
        (supportedSmoothing_zero (ε := ε) hRp f ((y,v),b) hy.le).symm

lemma bounded_spatialSlice_integrable (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (v : Circle) (b : ZMod 2) :
    IntegrableOn (fun x => f ((x,v),b)) Q.table := by
  have : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  exact (integrable_const H).mono'
    ((hm.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const)).aestronglyMeasurable)
    (Eventually.of_forall (fun x => hH ((x,v),b)))

lemma supportedSmoothing_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => supportedSmoothing Q ε R f ((x,v),b)) :=
  (vertexCutoff_contDiff Q R).smul (reflectedSmoothing_contDiff Q hε
    (bounded_spatialSlice_integrable Q hm hH v b)
    (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i v) (b+1)))

lemma supportedSmoothing_stronglyMeasurable (Q : Triangle) (ε R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (supportedSmoothing Q ε R f) :=
  (((vertexCutoff_contDiff Q R).continuous.comp (continuous_fst.comp continuous_fst)).stronglyMeasurable).smul
    (reflectedSmoothing_stronglyMeasurable Q ε hm)

lemma directS_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) (x : ℂ) : ‖directS Q ε f b v x‖ ≤ H := by
  unfold directS
  simpa only [one_mul] using norm_integral_le_kernel_bound
    (μ := volume.restrict Q.table) (fun y => kernel ε (x-y) • f ((y,v),b))
    (K := fun y => ENNReal.ofReal (kernel ε (x-y))) hH (by norm_num : (0 : ℝ) ≤ 1)
    (fun y => by
      rw [← ofReal_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonneg ε _), ENNReal.ofReal_mul (kernel_nonneg ε _)]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,v),b))) _)
    (by simpa only [ENNReal.ofReal_one] using kernel_row_bound Q hε x)

lemma reflectedSmoothing_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothing Q ε f z‖ ≤ 4 * H := by
  unfold reflectedSmoothing
  calc
    _ ≤ ‖directS Q ε f z.2 z.1.2 z.1.1‖ + ∑ i : Fin 3, ‖reflectedS Q i ε f z.2 z.1.2 z.1.1‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ H + ∑ _i : Fin 3, H := by
      gcongr
      · exact directS_norm_bound Q hε hH hf _ _ _
      · rw [reflectedS_eq_directS]
        exact directS_norm_bound Q hε hH hf _ _ _
    _ = 4 * H := by simp; ring

lemma supportedSmoothing_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖supportedSmoothing Q ε R f z‖ ≤ 4 * H := by
  rw [supportedSmoothing, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
  calc
    _ ≤ 1 * (4 * H) := mul_le_mul (vertexCutoff_mem_Icc Q R _).2
      (reflectedSmoothing_norm_bound Q hε hH hf z) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end TriangularBilliards

end
end
end
end
end

end OAI
