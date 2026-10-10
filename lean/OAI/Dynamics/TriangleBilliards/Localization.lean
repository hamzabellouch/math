import OAI.Dynamics.TriangleBilliards.SecondDerivatives

namespace OAI

universe uA

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
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace TriangularBilliards.Analysis
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

def restrictL2 (E : Set A) (hE : MeasurableSet E) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => ((Lp.memLp u).indicator hE).toLp (E.indicator u)
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (u+v)).indicator hE).coeFn_toLp,
          ((Lp.memLp u).indicator hE).coeFn_toLp,
          ((Lp.memLp v).indicator hE).coeFn_toLp,
          Lp.coeFn_add u v,
          Lp.coeFn_add (((Lp.memLp u).indicator hE).toLp _) (((Lp.memLp v).indicator hE).toLp _)]
          with z h0 h1 h2 h3 h4
        simp only [Pi.add_apply] at h3 h4
        rw [h0, h4, h1, h2]
        by_cases hz : z ∈ E
        · simp only [indicator_of_mem hz]; exact h3
        · simp only [indicator_of_notMem hz, add_zero]
      map_smul' := fun c u => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • u)).indicator hE).coeFn_toLp,
          ((Lp.memLp u).indicator hE).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (((Lp.memLp u).indicator hE).toLp _)] with z h0 h1 h2 h3
        simp only [Pi.smul_apply] at h2 h3
        change _ = (c • (((Lp.memLp u).indicator hE).toLp _)) z
        rw [h0, h3, h1]
        by_cases hz : z ∈ E
        · simp only [indicator_of_mem hz]; exact h2
        · simp only [indicator_of_notMem hz, smul_zero] }
    1 (fun u => by
      simp only [one_mul]
      change ‖((Lp.memLp u).indicator hE).toLp _‖ ≤ ‖u‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [((Lp.memLp u).indicator hE).coeFn_toLp] with z hz
      rw [hz]
      exact norm_indicator_le_norm_self _ _)

lemma restrictL2_coe (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    (restrictL2 E hE u : A → ℂ) =ᵐ[μ] E.indicator u :=
  ((Lp.memLp u).indicator hE).coeFn_toLp

lemma restrictL2_selfadjoint (E : Set A) (hE : MeasurableSet E) (u v : Lp ℂ 2 μ) :
    inner ℂ (restrictL2 E hE u) v = inner ℂ u (restrictL2 E hE v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictL2_coe E hE u, restrictL2_coe E hE v] with z hu hv
  rw [hu, hv]
  by_cases hz : z ∈ E
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, inner_zero_left, inner_zero_right]

lemma restrictL2_fixed (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ)
    (hu : ∀ᵐ z ∂μ, z ∉ E → u z = 0) : restrictL2 E hE u = u := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE u, hu] with z hz hzz
  rw [hz]
  by_cases hm : z ∈ E
  · exact indicator_of_mem hm _
  · simp only [indicator_of_notMem hm, hzz hm]

lemma restrictL2_commute (E : Set A) (hE : MeasurableSet E)
    (ρ : A → A) (hρ : MeasurePreserving ρ μ μ) (he : ∀ z, ρ z ∈ E ↔ z ∈ E)
    (u : Lp ℂ 2 μ) :
    restrictL2 E hE (Lp.compMeasurePreserving ρ hρ u) =
      Lp.compMeasurePreserving ρ hρ (restrictL2 E hE u) := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE (Lp.compMeasurePreserving ρ hρ u),
    Lp.coeFn_compMeasurePreserving u hρ,
    Lp.coeFn_compMeasurePreserving (restrictL2 E hE u) hρ,
    hρ.quasiMeasurePreserving.ae (restrictL2_coe E hE u)] with z h0 h1 h2 h3
  rw [h0, h2]
  change _ = restrictL2 E hE u (ρ z)
  rw [h3]
  by_cases hz : z ∈ E
  · rw [indicator_of_mem hz, indicator_of_mem ((he z).mpr hz)]
    exact h1
  · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz ((he z).mp h))]

lemma restrictL2_norm (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    ‖restrictL2 E hE u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [restrictL2_coe E hE u] with z hz
  rw [hz]
  exact norm_indicator_le_norm_self _ _

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis MeasureTheory Filter Set
open scoped ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma spatialRestriction_commute (Q : Triangle) (E : Set ℂ) (hE : MeasurableSet E)
    (θ : AddCircle (2 * Real.pi)) (u : Lp ℂ 2 (doubleMeasure Q)) :
    restrictL2 {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
        ((angularCircleAction Q).act θ u) =
      (angularCircleAction Q).act θ
        (restrictL2 {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst) u) := by
  exact restrictL2_commute _ _ (doubleRotate θ.toCircle)
    (measurePreserving_doubleRotate Q θ.toCircle) (fun _ => Iff.rfl) u

/-- The localized energy bound on the actual smooth core. Every generator
and Fourier projection here is that of the actual billiard double. -/
lemma seam_localized_energy {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q))
    (E : Set ℂ) (hE : MeasurableSet E)
    (hX : ∀ᵐ z ∂doubleMeasure Q, z.1.1 ∉ E → xDerivative f z = 0) (j : ℤ) :
    let hx := xDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let hy := yDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let R := restrictL2 (μ := doubleMeasure Q) {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
    ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
      (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dx ∧
      (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dy ∧
      ‖dx‖ ^ 2 ≤ 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ ∧
      ‖dy‖ ^ 2 ≤ 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ := by
  dsimp only
  let hx := xDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let R := restrictL2 (μ := doubleMeasure Q) {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
  let a := (1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)
  let b := (1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)
  have hab : a + b = hx.toLp _ := by dsimp [a,b]; module
  have hsub : a - b = (-Complex.I) • hy.toLp _ := by dsimp [a,b]; module
  have hRx : R (hx.toLp _) = hx.toLp _ := by
    apply restrictL2_fixed
    filter_upwards [hx.coeFn_toLp,hX] with z hz hh
    simpa only [hz, mem_ofPred_eq] using hh
  have hn (k : ℤ) : ‖(angularCircleAction Q).projection (k+2) a‖ =
      ‖(angularCircleAction Q).projection k b‖ := by
    have hh := seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hf (k+1)
    have hi : k + 1 + 1 = k + 2 := by omega
    simpa only [hi, add_sub_cancel_right] using hh
  have hh := (angularCircleAction Q).localized_CR_energy a b j R
    (spatialRestriction_commute Q E hE) (restrictL2_selfadjoint _ _)
    (by rw [hab]; exact hRx) hn
  have hRsub : ‖R (a-b)‖ = ‖R (hy.toLp _)‖ := by
    rw [hsub, map_smul, norm_smul, norm_neg, Complex.norm_I, one_mul]
  rw [hab, hRsub] at hh
  have hcr := seam_rotationalCR hs (fun v b => (hd v b).differentiable (by simp)) hC hf hx hy
  have hg := hcr.projection j
  have heq : ‖(angularCircleAction Q).projection (j+1) a‖ =
      ‖(angularCircleAction Q).projection (j-1) b‖ :=
    seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hf j
  let da := (angularCircleAction Q).projection (j+1) a
  let db := (angularCircleAction Q).projection (j-1) b
  refine ⟨da+db, Complex.I • (da-db), hg.1, hg.2, ?_, ?_⟩
  · have hl : ‖da+db‖ ≤ 2 * ‖da‖ := by
      calc _ ≤ ‖da‖ + ‖db‖ := norm_add_le _ _
           _ = _ := by rw [← heq]; ring
    calc
      _ ≤ (2*‖da‖)^2 := by gcongr
      _ = 4*‖da‖^2 := by ring
      _ ≤ _ := by linarith [hh]
  · have hl : ‖Complex.I • (da-db)‖ ≤ 2 * ‖da‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      calc _ ≤ ‖da‖ + ‖db‖ := norm_sub_le _ _
           _ = _ := by rw [← heq]; ring
    calc
      _ ≤ (2*‖da‖)^2 := by gcongr
      _ = 4*‖da‖^2 := by ring
      _ ≤ _ := by linarith [hh]

end TriangularBilliards

namespace TriangularBilliards
open MeasureTheory Set
namespace Triangle
lemma clearance_sublevel (Q : Triangle) (R : ℝ) :
    {x | Q.clearance x ≤ R} = ⋃ i : Fin 3, Metric.closedBall (Q.vertex i) R := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨i, rfl⟩, hi⟩ := (finite_range Q.vertex).isCompact.exists_infDist_eq_dist
      (range_nonempty Q.vertex) x
    exact mem_iUnion.mpr ⟨i, by simpa only [Metric.mem_closedBall, ← hi, clearance, mem_ofPred_eq] using hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact le_trans (Metric.infDist_le_dist_of_mem (mem_range_self i)) hi

lemma clearance_sublevel_measurable (Q : Triangle) (R : ℝ) :
    MeasurableSet {x | Q.clearance x ≤ R} :=
  measurableSet_le Q.clearance_lipschitz.continuous.measurable measurable_const

lemma clearance_area_bound (Q : Triangle) (R : ℝ) :
    volume {x | Q.clearance x ≤ R} ≤
      3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞) := by
  rw [Q.clearance_sublevel]
  calc
    volume (⋃ i : Fin 3, Metric.closedBall (Q.vertex i) R) ≤
      ∑' i : Fin 3, volume (Metric.closedBall (Q.vertex i) R) := measure_iUnion_le _
    _ = 3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞) := by
      simp only [Complex.volume_closedBall, tsum_fintype, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Triangle

/-- The small-tip neighborhood on the actual oriented double. -/
def unsafeSet (Q : Triangle) (R : ℝ) : Set DoublePhase :=
  {z | Q.clearance z.1.1 ≤ R}

lemma unsafeSet_measurable (Q : Triangle) (R : ℝ) : MeasurableSet (unsafeSet Q R) :=
  (Q.clearance_sublevel_measurable R).preimage measurable_fst.fst

lemma unsafeSet_measure_bound (Q : Triangle) (R : ℝ) :
    doubleMeasure Q (unsafeSet Q R) ≤
      (volume Q.table)⁻¹ * (3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞)) := by
  have he : unsafeSet Q R = ({x : ℂ | Q.clearance x ≤ R} ×ˢ (univ : Set Circle)) ×ˢ
      (univ : Set (ZMod 2)) := by ext z; simp only [unsafeSet, mem_ofPred_eq, mem_prod,
      mem_univ, and_true]
  rw [he, doubleMeasure, Measure.prod_prod, measure_univ, mul_one,
    phaseMeasure, Measure.prod_prod, measure_univ, mul_one, Measure.smul_apply, smul_eq_mul]
  gcongr
  calc
    volume.restrict Q.table {x | Q.clearance x ≤ R} ≤ volume {x | Q.clearance x ≤ R} :=
      Measure.restrict_apply_le _ _
    _ ≤ _ := Q.clearance_area_bound R

end TriangularBilliards

namespace TriangularBilliards.Analysis
open MeasureTheory Filter Set
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}
lemma restrictL2_norm_of_bounded (E : Set A) (hE : MeasurableSet E) (hμE : μ E ≠ ⊤)
    {u : Lp ℂ 2 μ} {H : ℝ} (hH : 0 ≤ H) (hu : ∀ᵐ z ∂μ, ‖u z‖ ≤ H) :
    ‖restrictL2 E hE u‖ ≤ H * (μ E).toReal ^ (1/2 : ℝ) := by
  calc
    _ ≤ ‖indicatorConstLp 2 hE hμE (H : ℂ)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hu,restrictL2_coe E hE u,
        indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hμE) (c := (H : ℂ))] with z hz he hc
      rw [he,hc]
      by_cases h : z ∈ E
      · simpa only [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hH] using hz
      · simp only [indicator_of_notMem h, le_refl]
    _ = _ := by rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
                simp [Complex.norm_real, abs_of_nonneg hH, Measure.real]

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma vertexCutoff_fderiv_zero_of_large (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : 2 * R < Q.clearance x) : fderiv ℝ (vertexCutoff Q R) x = 0 := by
  have he : vertexCutoff Q R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [((isOpen_lt continuous_const Q.clearance_lipschitz.continuous).mem_nhds hx)] with y hy
    exact vertexCutoff_one Q hR hy.le
  rw [he.fderiv_eq, fderiv_const_apply]

lemma supportedSmoothing_invariant_x_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, z ∉ unsafeSet Q A →
      xDerivative (supportedSmoothing Q ε R f) z = 0 := by
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  filter_upwards [invariant_smoothing_direction_zero Q hε hR hsmall hA hm hf hfi hH] with z hz hza
  have hb : A < Q.clearance z.1.1 := lt_of_not_ge hza
  have hc : 2 * R < Q.clearance z.1.1 := by linarith
  rw [supportedSmoothing_xDerivative Q hε R hm hH,
    supportedSmoothingGradient, vertexCutoff_fderiv_zero_of_large Q hRp hc,
    vertexCutoff_one Q hRp hc.le, one_smul, ContinuousLinearMap.zero_smulRight, add_zero]
  exact hz hb.le

lemma unsafeSet_real_measure_bound (Q : Triangle) {R : ℝ} (hR : 0 ≤ R) :
    (doubleMeasure Q (unsafeSet Q R)).toReal ≤
      ((volume Q.table).toReal)⁻¹ * (3 * R ^ 2 * Real.pi) := by
  have ht : (volume Q.table)⁻¹ * (3 * (ENNReal.ofReal R)^2 * (NNReal.pi : ℝ≥0∞)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr Q.area_pos.ne') (by finiteness)
  have hh := ENNReal.toReal_mono ht (unsafeSet_measure_bound Q R)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hR, ENNReal.coe_toReal, NNReal.coe_real_pi] using hh

/-- Generic localized gradient control on an actual smooth seam field, with
its exact tip-neighborhood measure retained. -/
lemma seam_tip_energy {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q)) (A : ℝ)
    (hX : ∀ᵐ z ∂doubleMeasure Q, z ∉ unsafeSet Q A → xDerivative f z = 0) (j : ℤ) :
    ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
      (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dx ∧
      (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dy ∧
      ‖dx‖ ^ 2 ≤ 4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal ∧
      ‖dy‖ ^ 2 ≤ 4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal := by
  let hx := xDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let R := restrictL2 (μ := doubleMeasure Q) (unsafeSet Q A) (unsafeSet_measurable Q A)
  have hxb : ∀ᵐ z ∂doubleMeasure Q, ‖hx.toLp _ z‖ ≤ (C : ℝ) := by
    filter_upwards [hx.coeFn_toLp] with z hz
    rw [hz]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [Circle.norm_coe, mul_one]; exact hC z.1.1 z.1.2 z.2)
  have hyb : ∀ᵐ z ∂doubleMeasure Q, ‖hy.toLp _ z‖ ≤ (C : ℝ) := by
    filter_upwards [hy.coeFn_toLp] with z hz
    rw [hz]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [norm_transverseVelocity, mul_one]; exact hC z.1.1 z.1.2 z.2)
  have hrx : R (hx.toLp _) = hx.toLp _ := by
    apply restrictL2_fixed
    filter_upwards [hx.coeFn_toLp,hX] with z hz hh
    simpa only [hz] using hh
  have hxn : ‖hx.toLp _‖ ≤ (C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ) := by
    rw [← hrx]
    exact restrictL2_norm_of_bounded _ _ (measure_ne_top _ _) C.coe_nonneg hxb
  have hyn := restrictL2_norm_of_bounded (unsafeSet Q A) (unsafeSet_measurable Q A)
    (measure_ne_top _ _) C.coe_nonneg hyb
  obtain ⟨dx,dy,hgx,hgy,hbx,hby⟩ := seam_localized_energy hs hm hd hC hD hf
    {x | Q.clearance x ≤ A} (Q.clearance_sublevel_measurable A) hX j
  have hmass : ((doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ))^2 =
      (doubleMeasure Q (unsafeSet Q A)).toReal := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hb : 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ ≤
      4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal := by
    calc
      _ ≤ 4 * ((C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ)) *
          ((C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ)) := by
        gcongr
      _ = _ := by nlinarith [hmass]
  exact ⟨dx,dy,hgx,hgy,hbx.trans hb,hby.trans hb⟩

end TriangularBilliards

end
end
end
end
end
end
end
end
end

end OAI
