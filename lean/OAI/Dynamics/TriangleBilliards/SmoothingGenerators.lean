import OAI.Dynamics.TriangleBilliards.DerivativeAdjoints

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

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped NNReal ContDiff

lemma supportedSmoothing_xDerivative (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : xDerivative (supportedSmoothing Q ε R f) z =
      supportedSmoothingGradient Q ε R f z (z.1.2 : ℂ) := by
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (z.1.2 : ℂ))
    (supportedSmoothing_hasFDerivAt Q hε R hm hH z.1.2 z.2 z.1.1).fderiv

lemma supportedSmoothing_fderiv_bound (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ≥0, ∀ x v b, ‖fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b)) x‖ ≤ C := by
  obtain ⟨D,hD,hDb⟩ := exists_vertexCutoff_derivative_bound
  have hH : 0 ≤ H := (norm_nonneg _).trans (hf ((0,1),0))
  let C := 4 * derivativeMass * H / ε + (D / R) * (4 * H)
  have hC : 0 ≤ C := by
    have := derivativeMass_nonneg
    dsimp [C]
    positivity
  refine ⟨⟨C,hC⟩, fun x v b => ?_⟩
  rw [(supportedSmoothing_hasFDerivAt Q hε R hm hf v b x).fderiv]
  exact supportedSmoothingGradient_norm_bound Q hε hH hf (hDb Q R hR) ((x,v),b)

lemma supportedSmoothing_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    MemLp (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (supportedSmoothing_stronglyMeasurable Q ε R hm).aestronglyMeasurable (4*H)
  exact Filter.Eventually.of_forall (supportedSmoothing_norm_bound Q hε R
    ((norm_nonneg _).trans (hf ((0,1),0))) hf)

lemma supportedSmoothing_xDerivative_memLp (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    MemLp (xDerivative (supportedSmoothing Q ε R f)) 2 (doubleMeasure Q) := by
  have he : xDerivative (supportedSmoothing Q ε R f) =
      fun z => supportedSmoothingGradient Q ε R f z (z.1.2 : ℂ) :=
    funext (supportedSmoothing_xDerivative Q hε R hm hf)
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hR hm hf
  refine MemLp.of_bound ?_ (C : ℝ) ?_
  · rw [he]
    exact (isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((supportedSmoothingGradient_stronglyMeasurable Q ε R hm).prodMk
        ((show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
          continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable))).aestronglyMeasurable
  · filter_upwards [] with z
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [Circle.norm_coe, mul_one]
      exact hC z.1.1 z.1.2 z.2)

lemma supportedSmoothing_generator (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    let hs := supportedSmoothing_memLp Q hε R hm hf
    let hx := supportedSmoothing_xDerivative_memLp Q hε
      ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
    (geodesicHilbertFlow Q).HasGenerator (hs.toLp _) (hx.toLp _) := by
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε
    ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
  apply seam_geodesic_generator (supportedSmoothing_seam Q hε hR hsmall f)
    (fun v b => (supportedSmoothing_contDiff Q hε R hm hf v b).differentiable (by simp)) hC

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma supportedSmoothing_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) {z : DoublePhase}
    (hz : z.1.1 ∈ Q.table) :
    supportedSmoothing Q ε R f z = reflectedSmoothing Q ε f z := by
  by_cases hr : 2 * R ≤ Q.clearance z.1.1
  · simp only [supportedSmoothing, vertexCutoff_one Q hR hr, one_smul]
  · have hzero := reflectedSmoothing_zero_near_tips Q hε hf hz (by linarith)
    simp only [supportedSmoothing, hzero, smul_zero]

lemma supportedSmoothing_derivative_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase} (hz : z.1.1 ∈ Q.table) :
    xDerivative (supportedSmoothing Q ε R f) z = reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) := by
  have he : (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1]
      (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) := by
    filter_upwards [isOpen_interior.eventually_mem hz] with y hy
    exact supportedSmoothing_eq_of_supported Q hε hR hA hf hy
  change fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) z.1.1 _ = _
  rw [he.fderiv_eq]
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (z.1.2 : ℂ))
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv

lemma reflectedSmoothing_direction_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) 2 (doubleMeasure Q) :=
  gradientApply_memLp (reflectedSmoothingGradient_memLp Q hε hm hf)
    ((show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
          continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable)
    (fun _z => (Circle.norm_coe _).le)

lemma reflectedSmoothing_supported_generator (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (hf : MemLp f 2 (doubleMeasure Q)) (hs : SpatiallyZero Q A f) :
    (geodesicHilbertFlow Q).HasGenerator
      ((reflectedSmoothing_memLp Q hε hm hf).toLp _)
      ((reflectedSmoothing_direction_memLp Q hε hm hf).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have h := supportedSmoothing_generator Q hε hR hsmall hm hH
  have h₁ := (supportedSmoothing_memLp Q hε R hm hH).toLp_congr
    (reflectedSmoothing_memLp Q hε hm hf) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_eq_of_supported Q hε hRp hA hs hz)
  have h₂ := (supportedSmoothing_xDerivative_memLp Q hε hRp hm hH).toLp_congr
    (reflectedSmoothing_direction_memLp Q hε hm hf) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_derivative_eq_of_supported Q hε hRp hA hs hm hH hz)
  change (geodesicHilbertFlow Q).HasGenerator
    ((supportedSmoothing_memLp Q hε R hm hH).toLp _) _ at h
  rwa [h₁, h₂] at h

lemma integral_pairing_toLp {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z, f z * conj (g z) ∂μ) = inner ℂ (hg.toLp g) (hf.toLp f) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hz hzz
  simp only [hz, hzz, RCLike.inner_apply]

/-- Exact local kernel-transport commutation for a bounded invariant field,
expressed against arbitrary bounded fields with a sufficient vertex margin. -/
lemma invariant_smoothing_direction_pairing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) = 0 := by
  have h := reflectedSmoothingGradient_adjoint Q hε
    (V := fun c => (c.1 : ℂ)) (show Continuous (fun c : DirectionParity => (c.1 : ℂ)) from
      continuous_subtype_val.comp continuous_fst).stronglyMeasurable
    (fun c => (Circle.norm_coe _).le) (fun i c => rfl) hfm hgm hf hg
  have hgen := reflectedSmoothing_supported_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (geodesicHilbertFlow Q).generator_skew hgen hfi
  simp only [inner_zero_right, zero_add] at hsk
  rw [h, integral_pairing_toLp hf (reflectedSmoothing_direction_memLp Q hε hgm hg), hsk, neg_zero]

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma reflectedSmoothing_direction_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)‖ ≤
      4 * derivativeMass * H / ε := by
  calc
    _ ≤ ‖reflectedSmoothingGradient Q ε f z‖ * ‖(z.1.2 : ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by rw [Circle.norm_coe, mul_one]; exact reflectedSmoothingGradient_norm_bound Q hε hH hf z

lemma reflectedSmoothing_direction_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) :=
  isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((reflectedSmoothingGradient_stronglyMeasurable Q ε hm).prodMk
      (show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
        continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable)

/-- The actual local X-commutation equation for a bounded invariant field.
No local distributional transport statement is used as an extra hypothesis. -/
lemma invariant_smoothing_direction_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) = 0 := by
  let D : DoublePhase → ℂ := fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)
  let E : Set DoublePhase := {z | A ≤ Q.clearance z.1.1}
  let g : DoublePhase → ℂ := E.indicator D
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const
      (Q.clearance_lipschitz.continuous.measurable.comp (measurable_fst.fst))
  have hDm : StronglyMeasurable D := reflectedSmoothing_direction_stronglyMeasurable Q ε hfm
  have hDp : MemLp D 2 (doubleMeasure Q) := reflectedSmoothing_direction_memLp Q hε hfm hf
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hgb : ∀ z, ‖g z‖ ≤ 4 * derivativeMass * H / ε := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_mem hz]
      exact reflectedSmoothing_direction_norm_bound Q hε hH₀ hH z
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_notMem hz, norm_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) hH₀) hε.le
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact Set.indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hp := invariant_smoothing_direction_pairing_zero Q hε hR hsmall hA hfm hgm hf hgp hfi hgb hgs
  have he : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    rw [← hp]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ E
    · simp only [g, Set.indicator_of_mem hz, D]
    · simp only [g, Set.indicator_of_notMem hz, map_zero, mul_zero]
  rw [integral_pairing_toLp hgp hgp, inner_self_eq_zero] at he
  have hgz : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [he] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgz] with z hz hza
  change D z = 0
  simpa only [g, Set.indicator_of_mem (show z ∈ E from hza), Pi.zero_apply] using hz

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped ComplexConjugate

lemma pairing_add_sum_symmetric {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g d e : A → ℂ} {r s : Fin 3 → A → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hd : MemLp d 2 μ) (he : MemLp e 2 μ)
    (hr : ∀ i, MemLp (r i) 2 μ) (hs : ∀ i, MemLp (s i) 2 μ)
    (h0 : (∫ z, d z * conj (g z) ∂μ) = (∫ z, f z * conj (e z) ∂μ))
    (hi : ∀ i, (∫ z, r i z * conj (g z) ∂μ) = (∫ z, f z * conj (s i z) ∂μ)) :
    (∫ z, (d z + ∑ i, r i z) * conj (g z) ∂μ) =
      (∫ z, f z * conj (e z + ∑ i, s i z) ∂μ) := by
  have hD : Integrable (fun z => d z * conj (g z)) μ := hd.integrable_mul (memLp_conj hg)
  have hE : Integrable (fun z => f z * conj (e z)) μ := hf.integrable_mul (memLp_conj he)
  have hR (i) : Integrable (fun z => r i z * conj (g z)) μ := (hr i).integrable_mul (memLp_conj hg)
  have hS (i) : Integrable (fun z => f z * conj (s i z)) μ := hf.integrable_mul (memLp_conj (hs i))
  simp only [add_mul, Finset.sum_mul, map_add, map_sum, mul_add, Finset.mul_sum]
  rw [integral_add hD (integrable_finsetSum Finset.univ (fun i _ => hR i)),
    integral_add hE (integrable_finsetSum Finset.univ (fun i _ => hS i)),
    integral_finsetSum Finset.univ (fun i _ => hR i),
    integral_finsetSum Finset.univ (fun i _ => hS i), h0]
  simp only [hi]

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma spatialKernel_stronglyMeasurable (ε : ℝ) {R : ℂ → ℂ} (hR : Measurable R) :
    StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => kernel ε (p.1.1-R p.2)) :=
  ((kernel_contDiff ε).continuous.measurable.comp
    (measurable_fst.fst.sub (hR.comp measurable_snd))).stronglyMeasurable

lemma directS_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, directS Q ε f z.2 z.1.2 z.1.1 * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (directS Q ε g z.2 z.1.2 z.1.1) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous (kernel_contDiff ε).continuous
  exact doubleKernel_adjoint Q (J := id) (MeasurePreserving.id _) MeasurableEmbedding.id (fun _ => rfl)
    (spatialKernel_stronglyMeasurable ε measurable_id) (spatialKernel_stronglyMeasurable ε measurable_id)
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-y))
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-y))
    (fun x y _ => kernel_swap ε x y) hfm hgm hf hg

lemma reflectedS_adjoint (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedS Q i ε f z.2 z.1.2 z.1.1 * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (reflectedS Q i ε g z.2 z.1.2 z.1.1) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous (kernel_contDiff ε).continuous
  exact doubleKernel_adjoint Q (measurePreserving_directionParity Q i)
    (measurableEmbedding_directionParity Q i) (directionParityReflection_involutive Q i)
    (spatialKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable)
    (spatialKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable)
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-wallReflection Q i y))
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-wallReflection Q i y))
    (fun x y _ => kernel_wall_swap Q i ε x y) hfm hgm hf hg

lemma directS_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => directS Q ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) :=
  (directS_eLpNorm Q hε hfm).trans_lt hf.eLpNorm_lt_top

lemma reflectedS_memLp (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => reflectedS Q i ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) :=
  (reflectedS_eLpNorm Q i hε hfm).trans_lt hf.eLpNorm_lt_top

lemma reflectedSmoothing_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothing Q ε f z * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (reflectedSmoothing Q ε g z) ∂doubleMeasure Q) := by
  exact pairing_add_sum_symmetric hf hg (directS_memLp Q hε hfm hf) (directS_memLp Q hε hgm hg)
    (fun i => reflectedS_memLp Q i hε hfm hf) (fun i => reflectedS_memLp Q i hε hgm hg)
    (directS_adjoint Q hε hfm hgm hf hg) (fun i => reflectedS_adjoint Q i hε hfm hgm hf hg)

end TriangularBilliards

end
end
end
end
end
end

end OAI
