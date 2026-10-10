import OAI.Dynamics.TriangleBilliards.KernelAdjoints

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
open scoped ComplexConjugate

lemma directionalKernel_stronglyMeasurable (ε : ℝ) {R : ℂ → ℂ} (hR : Measurable R)
    {V : DirectionParity → ℂ} (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ =>
      fderiv ℝ (kernel ε) (p.1.1-R p.2) (V p.1.2)) := by
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    (((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
      (measurable_fst.fst.sub (hR.comp measurable_snd))).stronglyMeasurable).prodMk
      (hV.comp_measurable measurable_fst.snd))

lemma directionalKernel_bounded {ε : ℝ} (hε : 0 < ε) (R : ℂ → ℂ)
    {V : DirectionParity → ℂ} (hV : ∀ c, ‖V c‖ ≤ 1) :
    ∃ K : ℝ, ∀ x y c, |fderiv ℝ (kernel ε) (x-R y) (V c)| ≤ K := by
  obtain ⟨K,hK⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  refine ⟨K,fun x y c => ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (kernel ε) (x-R y)‖ * ‖V c‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (kernel ε) (x-R y)‖ * 1 := mul_le_mul_of_nonneg_left (hV c) (norm_nonneg _)
    _ ≤ K := by simpa only [mul_one] using hK (x-R y)

lemma directDirectional_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q id (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) f z *
      conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q id
        (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) g z) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := directionalKernel_bounded hε id hV
  exact doubleKernel_skew Q (MeasurePreserving.id _) MeasurableEmbedding.id (fun _ => rfl)
    (directionalKernel_stronglyMeasurable ε measurable_id hVm) hK
    (fun x y c => kernel_derivative_swap ε x y (V c)) hfm hgm hf hg

lemma reflectedDirectional_adjoint (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    (hVR : ∀ c, reflect (Q.tangent i) (V c) = V (directionParityReflection Q i c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q (directionParityReflection Q i)
      (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) f z *
      conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q (directionParityReflection Q i)
        (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) g z) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := directionalKernel_bounded hε (wallReflection Q i) hV
  apply doubleKernel_skew Q (measurePreserving_directionParity Q i)
    (measurableEmbedding_directionParity Q i) (directionParityReflection_involutive Q i)
    (directionalKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable hVm)
    hK _ hfm hgm hf hg
  intro x y c
  simpa only [hVR] using kernel_wall_derivative_swap Q i ε x y (V c)

lemma directGradS_apply_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (V : DirectionParity → ℂ) {f : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (fun z => directGradS Q ε f z (V (z.1.2,z.2))) =ᵐ[doubleMeasure Q]
      doubleKernel Q id (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) f := by
  filter_upwards [directGradS_integrable_ae Q hε hfm (hf.integrable (by norm_num))] with z hz
  exact ContinuousLinearMap.integral_apply hz (V (z.1.2,z.2))

lemma reflectedGradS_apply_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (V : DirectionParity → ℂ) {f : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (fun z => reflectedGradS Q i ε f z (V (z.1.2,z.2))) =ᵐ[doubleMeasure Q]
      doubleKernel Q (directionParityReflection Q i)
        (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) f := by
  filter_upwards [reflectedGradS_integrable_ae Q i hε hfm (hf.integrable (by norm_num))] with z hz
  exact ContinuousLinearMap.integral_apply hz (V (z.1.2,z.2))

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped ComplexConjugate

lemma gradientApply_memLp {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {F : A → ℂ →L[ℝ] ℂ} (hF : MemLp F 2 μ)
    {V : A → ℂ} (hV : StronglyMeasurable V) (hVb : ∀ z, ‖V z‖ ≤ 1) :
    MemLp (fun z => F z (V z)) 2 μ := by
  apply hF.norm.mono'
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hF.aestronglyMeasurable.prodMk hV.aestronglyMeasurable))
  exact Eventually.of_forall fun z =>
    (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_left (hVb z) (norm_nonneg _)).trans_eq (mul_one _))

lemma pairing_add_sum {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g d e : A → ℂ} {r s : Fin 3 → A → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hd : MemLp d 2 μ) (he : MemLp e 2 μ)
    (hr : ∀ i, MemLp (r i) 2 μ) (hs : ∀ i, MemLp (s i) 2 μ)
    (h0 : (∫ z, d z * conj (g z) ∂μ) = -(∫ z, f z * conj (e z) ∂μ))
    (hi : ∀ i, (∫ z, r i z * conj (g z) ∂μ) = -(∫ z, f z * conj (s i z) ∂μ)) :
    (∫ z, (d z + ∑ i, r i z) * conj (g z) ∂μ) =
      -(∫ z, f z * conj (e z + ∑ i, s i z) ∂μ) := by
  have hD : Integrable (fun z => d z * conj (g z)) μ := hd.integrable_mul (memLp_conj hg)
  have hE : Integrable (fun z => f z * conj (e z)) μ := hf.integrable_mul (memLp_conj he)
  have hR (i) : Integrable (fun z => r i z * conj (g z)) μ := (hr i).integrable_mul (memLp_conj hg)
  have hS (i) : Integrable (fun z => f z * conj (s i z)) μ := hf.integrable_mul (memLp_conj (hs i))
  simp only [add_mul, Finset.sum_mul, map_add, map_sum, mul_add, Finset.mul_sum]
  rw [integral_add hD (integrable_finsetSum Finset.univ (fun i _ => hR i)),
    integral_add hE (integrable_finsetSum Finset.univ (fun i _ => hS i)),
    integral_finsetSum Finset.univ (fun i _ => hR i),
    integral_finsetSum Finset.univ (fun i _ => hS i), h0]
  simp only [hi, Finset.sum_neg_distrib, neg_add_rev]
  ring

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped ComplexConjugate

lemma directGradS_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (directGradS Q ε f) 2 (doubleMeasure Q) :=
  (directGradS_eLpNorm Q hε hfm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

lemma reflectedGradS_memLp (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedGradS Q i ε f) 2 (doubleMeasure Q) :=
  (reflectedGradS_eLpNorm Q i hε hfm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- Adjoint identity for the actual unfolded gradient kernel on the complete
L² space. It holds in particular after pairing against a supported field,
without taking any derivatives of that field. -/
lemma reflectedSmoothingGradient_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    (hVR : ∀ i c, reflect (Q.tangent i) (V c) = V (directionParityReflection Q i c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothingGradient Q ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedSmoothingGradient Q ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
  have hm : StronglyMeasurable (fun z : DoublePhase => V (z.1.2,z.2)) :=
    hVm.comp_measurable (measurable_fst.snd.prodMk measurable_snd)
  have hdF := gradientApply_memLp (directGradS_memLp Q hε hfm hf) hm (fun z => hV (z.1.2,z.2))
  have hdG := gradientApply_memLp (directGradS_memLp Q hε hgm hg) hm (fun z => hV (z.1.2,z.2))
  have hrF (i) := gradientApply_memLp (reflectedGradS_memLp Q i hε hfm hf) hm (fun z => hV (z.1.2,z.2))
  have hrG (i) := gradientApply_memLp (reflectedGradS_memLp Q i hε hgm hg) hm (fun z => hV (z.1.2,z.2))
  have hd : (∫ z, directGradS Q ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (directGradS Q ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
    have h := directDirectional_adjoint Q hε hVm hV hfm hgm hf hg
    convert h using 1
    · apply integral_congr_ae
      filter_upwards [directGradS_apply_ae Q hε V hfm hf] with z hz
      rw [hz]
    · congr 1
      apply integral_congr_ae
      filter_upwards [directGradS_apply_ae Q hε V hgm hg] with z hz
      rw [hz]
  have hr (i) : (∫ z, reflectedGradS Q i ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedGradS Q i ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
    have h := reflectedDirectional_adjoint Q i hε hVm hV (hVR i) hfm hgm hf hg
    convert h using 1
    · apply integral_congr_ae
      filter_upwards [reflectedGradS_apply_ae Q i hε V hfm hf] with z hz
      rw [hz]
    · congr 1
      apply integral_congr_ae
      filter_upwards [reflectedGradS_apply_ae Q i hε V hgm hg] with z hz
      rw [hz]
  have hh := pairing_add_sum hf hg hdF hdG hrF hrG hd hr
  simpa only [reflectedSmoothingGradient, Pi.add_apply, Finset.sum_apply,
    _root_.add_apply, _root_.sum_apply] using hh

end TriangularBilliards

namespace TriangularBilliards
open SpatialSmoothing Filter
open scoped Topology ContDiff

lemma directS_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,v),b)) Q.table) (x : ℂ) :
    HasFDerivAt (directS Q ε f b v) (directGradS Q ε f ((x,v),b)) x := by
  have h := ((directS_contDiff Q hε hf).differentiable (by simp) x).hasFDerivAt
  rwa [directS_fderiv Q hε hf] at h

lemma kernel_wall_derivative_transfer (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (wallReflection Q i x-y) (reflect (Q.tangent i) V) =
      fderiv ℝ (kernel ε) (x-wallReflection Q i y) V := by
  rw [kernel_derivative_swap ε (wallReflection Q i x) y]
  exact (kernel_wall_derivative_swap Q i ε x y V).symm

lemma reflectedS_hasFDerivAt (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,reflectedDirection Q i v),b+1)) Q.table) (x : ℂ) :
    HasFDerivAt (reflectedS Q i ε f b v) (reflectedGradS Q i ε f ((x,v),b)) x := by
  rw [reflectedS_eq_directS]
  have h := (directS_hasFDerivAt Q hε hf (wallReflection Q i x)).comp x
    (wallReflection_hasFDerivAt Q i x)
  have he : reflectedGradS Q i ε f ((x,v),b) =
      (directGradS Q ε f ((wallReflection Q i x,reflectedDirection Q i v),b+1)).comp
        (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap := by
    obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
      ((kernel_contDiff ε).continuous_fderiv (by simp))
    have hi (a : ℂ) (J : ℂ → ℂ) (hJ : Measurable J) :
        Integrable (fun y => (fderiv ℝ (kernel ε) (a-J y)).smulRight
          (f ((y,reflectedDirection Q i v),b+1))) (volume.restrict Q.table) :=
      smulRight_integrable
        (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
          (measurable_const.sub hJ))
        (hm.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
        hf (fun y => hC _)
    ext V
    change (∫ y in Q.table, (fderiv ℝ (kernel ε) (x-wallReflection Q i y)).smulRight
      (f ((y,reflectedDirection Q i v),b+1))) V =
      (∫ y in Q.table, (fderiv ℝ (kernel ε) (wallReflection Q i x-y)).smulRight
      (f ((y,reflectedDirection Q i v),b+1))) (reflect (Q.tangent i) V)
    have hi' := hi (wallReflection Q i x) id measurable_id
    simp only [id_eq] at hi'
    rw [ContinuousLinearMap.integral_apply (hi x _ (wallReflection_contDiff Q i).continuous.measurable),
      ContinuousLinearMap.integral_apply hi']
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [ContinuousLinearMap.smulRight_apply, kernel_wall_derivative_transfer]
  rw [he]
  exact h

lemma reflectedSmoothing_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,v),b)) Q.table)
    (hfr : ∀ i, IntegrableOn (fun y => f ((y,reflectedDirection Q i v),b+1)) Q.table)
    (x : ℂ) :
    HasFDerivAt (fun y => reflectedSmoothing Q ε f ((y,v),b))
      (reflectedSmoothingGradient Q ε f ((x,v),b)) x := by
  exact (directS_hasFDerivAt Q hε hf x).add
    (HasFDerivAt.fun_sum (fun i _ => reflectedS_hasFDerivAt Q i hε hm (hfr i) x))

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology NNReal ContDiff

lemma vertexCutoffFactor_derivative_bound {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ raw x‖ ≤ C) (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (i : Fin 3) (x : ℂ) : ‖fderiv ℝ (vertexCutoffFactor Q R i) x‖ ≤ C / (2 * R) := by
  let A : ℂ →L[ℝ] ℂ := (2 * R)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hA : HasFDerivAt (fun y : ℂ => (2 * R)⁻¹ • (y-Q.vertex i)) A x :=
    by
      convert ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const (Q.vertex i)).const_smul ((2 * R)⁻¹ : ℝ) using 1
      rfl
  have hd := ((raw_contDiff.differentiable (by simp)) _).hasFDerivAt.comp x hA
  have he := hd.const_sub 1
  rw [show fderiv ℝ (vertexCutoffFactor Q R i) x =
    -(fderiv ℝ raw ((2*R)⁻¹ • (x-Q.vertex i))).comp A from he.fderiv, norm_neg]
  calc
    _ ≤ ‖fderiv ℝ raw ((2*R)⁻¹ • (x-Q.vertex i))‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (2 * R)⁻¹ := by
      rw [show ‖A‖ = (2 * R)⁻¹ by
        simp only [A, norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
        exact abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
      exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.mpr (mul_nonneg (by norm_num) hR.le))
    _ = _ := (div_eq_mul_inv _ _).symm

lemma vertexCutoff_derivative_bound {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ raw x‖ ≤ C) (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (x : ℂ) : ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ 3 * C / (2 * R) := by
  classical
  change ‖fderiv ℝ (fun y => ∏ i : Fin 3, vertexCutoffFactor Q R i y) x‖ ≤ _
  rw [fderiv_finsetProd (fun i _ => (vertexCutoffFactor_contDiff Q R i).differentiable (by simp) x)]
  calc
    _ ≤ ∑ i : Fin 3, ‖(∏ j ∈ Finset.univ.erase i, vertexCutoffFactor Q R j x) •
      fderiv ℝ (vertexCutoffFactor Q R i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, C / (2 * R) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).1))]
      calc
        _ ≤ 1 * ‖fderiv ℝ (vertexCutoffFactor Q R i) x‖ :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_one₀
            (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).1)
            (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).2)) (norm_nonneg _)
        _ ≤ _ := by simpa using vertexCutoffFactor_derivative_bound hC Q hR i x
    _ = _ := by simp; ring

lemma exists_vertexCutoff_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : Triangle) (R : ℝ), 0 < R → ∀ x,
      ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ C / R := by
  obtain ⟨C,hC⟩ := (raw_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (raw_contDiff.continuous_fderiv (by simp))
  refine ⟨3*C/2, by have := (norm_nonneg _).trans (hC 0); positivity, ?_⟩
  intro Q R hR x
  convert vertexCutoff_derivative_bound hC Q hR x using 1
  ring

def supportedSmoothingGradient (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ)
    (z : DoublePhase) : ℂ →L[ℝ] ℂ :=
  vertexCutoff Q R z.1.1 • reflectedSmoothingGradient Q ε f z +
    (fderiv ℝ (vertexCutoff Q R) z.1.1).smulRight (reflectedSmoothing Q ε f z)

lemma supportedSmoothing_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) (x : ℂ) :
    HasFDerivAt (fun y => supportedSmoothing Q ε R f ((y,v),b))
      (supportedSmoothingGradient Q ε R f ((x,v),b)) x := by
  exact ((vertexCutoff_contDiff Q R).differentiable (by simp) x).hasFDerivAt.smul
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH v b)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i v) (b+1)) x)

lemma supportedSmoothingGradient_stronglyMeasurable (Q : Triangle) (ε R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (supportedSmoothingGradient Q ε R f) := by
  apply StronglyMeasurable.add
  · exact (((vertexCutoff_contDiff Q R).continuous.comp
      (continuous_fst.comp continuous_fst)).stronglyMeasurable).smul
      (reflectedSmoothingGradient_stronglyMeasurable Q ε hm)
  · exact smulRight_stronglyMeasurable
      ((((vertexCutoff_contDiff Q R).continuous_fderiv (by simp)).comp
        (continuous_fst.comp continuous_fst)).stronglyMeasurable)
      (reflectedSmoothing_stronglyMeasurable Q ε hm)

lemma reflectedSmoothingGradient_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothingGradient Q ε f z‖ ≤ 4 * derivativeMass * H / ε := by
  have h := scaled_gradient_norm_bound Q hε hH hf z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h
  exact (le_div_iff₀ hε).mpr (by nlinarith)

lemma supportedSmoothingGradient_norm_bound (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) {f : DoublePhase → ℂ} {H C : ℝ} (hH : 0 ≤ H)
    (hf : ∀ z, ‖f z‖ ≤ H) (hC : ∀ x, ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ C)
    (z : DoublePhase) : ‖supportedSmoothingGradient Q ε R f z‖ ≤
      4 * derivativeMass * H / ε + C * (4 * H) := by
  unfold supportedSmoothingGradient
  calc
    _ ≤ ‖vertexCutoff Q R z.1.1 • reflectedSmoothingGradient Q ε f z‖ +
      ‖(fderiv ℝ (vertexCutoff Q R) z.1.1).smulRight (reflectedSmoothing Q ε f z)‖ := norm_add_le _ _
    _ ≤ 4 * derivativeMass * H / ε + C * (4 * H) := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
        exact (mul_le_of_le_one_left (norm_nonneg _) (vertexCutoff_mem_Icc Q R _).2).trans
          (reflectedSmoothingGradient_norm_bound Q hε hH hf z)
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul (hC _) (reflectedSmoothing_norm_bound Q hε hH hf z)
          (norm_nonneg _) ((norm_nonneg _).trans (hC z.1.1))

end TriangularBilliards

end
end
end
end
end
end

end OAI
