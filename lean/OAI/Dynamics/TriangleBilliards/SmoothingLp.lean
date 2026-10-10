import OAI.Dynamics.TriangleBilliards.KernelBounds

namespace OAI

universe uAlpha uE uF

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace TriangularBilliards
open SpatialSmoothing
open Analytic

lemma double_lintegral_assoc (Q : Triangle) (F : DoublePhase → ℝ≥0∞) :
    ∫⁻ z, F z ∂doubleMeasure Q = (volume Q.table)⁻¹ *
      ∫⁻ p : ℂ × (Circle × ZMod 2), F ((p.1, p.2.1), p.2.2)
        ∂(volume.restrict Q.table).prod (angularMeasure.prod parityMeasure) := by
  simp only [doubleMeasure, phaseMeasure, Measure.prod_smul_left,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  exact (measurePreserving_prodAssoc (volume.restrict Q.table) angularMeasure parityMeasure).lintegral_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun p : ℂ × (Circle × ZMod 2) => F ((p.1, p.2.1), p.2.2))

lemma directS_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : SmoothPhase => directS Q ε f z.2 z.1.2 z.1.1) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      kernel ε (z.1.1 - y) • f ((y, z.1.2), z.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.fst.sub measurable_snd)).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd))
  exact h.integral_prod_right

lemma reflectedS_stronglyMeasurable (Q : Triangle) (i : Fin 3) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : SmoothPhase => reflectedS Q i ε f z.2 z.1.2 z.1.1) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      kernel ε (z.1.1 - wallReflection Q i y) •
        f ((y, reflectedDirection Q i z.1.2), z.2 + 1))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.fst.sub
        ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd))).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk ((measurePreserving_reflectedDirection Q i).measurable.comp
          measurable_fst.fst.snd)).prodMk (measurable_fst.snd.add_const 1)))
  exact h.integral_prod_right

lemma reflectedSmoothing_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedSmoothing Q ε f) := by
  apply (directS_stronglyMeasurable Q ε hf).add
  convert (Finset.stronglyMeasurable_sum Finset.univ
    (fun i _ => reflectedS_stronglyMeasurable Q i ε hf)) using 1
  ext z
  simp only [Finset.sum_apply]

lemma directS_l2sq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖directS Q ε f z.2 z.1.2 z.1.1‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  rw [double_lintegral_assoc, double_lintegral_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ => ENNReal.ofReal (kernel ε (x - y)))) :=
    ENNReal.measurable_ofReal.comp ((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.sub measurable_snd))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        kernel ε (p.1 - y) • f ((y, p.2.1), p.2.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.sub measurable_snd)).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hf.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (kernel_row_bound Q hε) (kernel_col_bound Q hε) hFm (fun x c y => by
      simp only [enorm_smul, Real.enorm_eq_ofReal (kernel_nonneg ε _), Function.comp_apply,
        le_refl])
  simpa only [one_mul, directS, Function.comp_apply] using h

lemma measurePreserving_directionParityReflection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (fun z : SmoothPhase =>
      ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)) (doubleMeasure Q) (doubleMeasure Q) := by
  convert ((MeasurePreserving.id ((volume Q.table)⁻¹ • volume.restrict Q.table)).prod
    (measurePreserving_reflectedDirection Q i)).prod (measurePreserving_parity_add 1) using 1
  · funext ⟨⟨x, v⟩, b⟩
    simp only [Prod.map_apply, id_eq, add_comm]
  · rfl
  · rfl

lemma reflectedS_l2sq (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖reflectedS Q i ε f z.2 z.1.2 z.1.1‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  let g : SmoothPhase → ℂ := fun z => f ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)
  have hg : StronglyMeasurable g := hf.comp_measurable
    (measurePreserving_directionParityReflection Q i).measurable
  have he : (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q) =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q :=
    (measurePreserving_directionParityReflection Q i).lintegral_comp (hf.enorm.pow_const 2)
  rw [← he, double_lintegral_assoc, double_lintegral_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal (kernel ε (x - wallReflection Q i y)))) :=
    ENNReal.measurable_ofReal.comp ((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd)))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        kernel ε (p.1 - wallReflection Q i y) • g ((y, p.2.1), p.2.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp
        measurable_snd))).stronglyMeasurable).smul
      (hg.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hg.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (reflected_kernel_row_bound Q i hε) (reflected_kernel_col_bound Q i hε) hFm (fun x c y => by
      simp only [enorm_smul, Real.enorm_eq_ofReal (kernel_nonneg ε _), Function.comp_apply,
        le_refl])
  simpa only [one_mul, reflectedS, g, Function.comp_apply] using h

lemma eLpNorm_two_mono_lintegral {α : Type uAlpha} {E : Type uE} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure α)
    {f : α → E} {g : α → F}
    (h : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) ≤ ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) :
    eLpNorm' f 2 μ ≤ eLpNorm' g 2 μ := by
  simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma directS_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (fun z : SmoothPhase => directS Q ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) ≤
      eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (directS_stronglyMeasurable Q ε hf).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable, ENNReal.toReal_ofNat]
    using eLpNorm_two_mono_lintegral _ (directS_l2sq Q hε hf)

lemma reflectedS_eLpNorm (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (fun z : SmoothPhase => reflectedS Q i ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) ≤
      eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (reflectedS_stronglyMeasurable Q i ε hf).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable, ENNReal.toReal_ofNat]
    using eLpNorm_two_mono_lintegral _ (reflectedS_l2sq Q i hε hf)

lemma reflectedSmoothing_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) ≤
      4 * eLpNorm f 2 (doubleMeasure Q) := by
  let d : SmoothPhase → ℂ := fun z => directS Q ε f z.2 z.1.2 z.1.1
  let r : Fin 3 → SmoothPhase → ℂ := fun i z => reflectedS Q i ε f z.2 z.1.2 z.1.1
  have he : reflectedSmoothing Q ε f = d + ∑ i, r i := by
    ext z
    simp only [reflectedSmoothing, Pi.add_apply, Finset.sum_apply, d, r]
  rw [he]
  calc
    _ ≤ eLpNorm d 2 (doubleMeasure Q) + eLpNorm (∑ i, r i) 2 (doubleMeasure Q) :=
      eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm f 2 (doubleMeasure Q) + ∑ i : Fin 3, eLpNorm (r i) 2 (doubleMeasure Q) :=
      add_le_add (directS_eLpNorm Q hε hf)
        (eLpNorm_sum_le (by norm_num))
    _ ≤ eLpNorm f 2 (doubleMeasure Q) + ∑ _i : Fin 3, eLpNorm f 2 (doubleMeasure Q) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i _ => reflectedS_eLpNorm Q i hε hf))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma reflectedSmoothing_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) := by
  exact (reflectedSmoothing_eLpNorm Q hε hf).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hf₂.eLpNorm_lt_top)

/-- The actual gradient convolution, as a bounded linear differential. -/
def directGradS (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) : SmoothPhase → (ℂ →L[ℝ] ℂ) :=
  fun z => ∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y, z.1.2), z.2))

def reflectedGradS (Q : Triangle) (i : Fin 3) (ε : ℝ)
    (f : SmoothPhase → ℂ) : SmoothPhase → (ℂ →L[ℝ] ℂ) :=
  fun z => ∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)).smulRight
    (f ((y, reflectedDirection Q i z.1.2), z.2 + 1))

def reflectedSmoothingGradient (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) :
    SmoothPhase → (ℂ →L[ℝ] ℂ) := directGradS Q ε f + ∑ i, reflectedGradS Q i ε f

lemma derivative_kernel_row_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := (lintegral_sub_left_eq_self
      (fun y : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) y‖) x).trans
        (kernel_derivative_lintegral hε)

lemma derivative_kernel_col_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ x : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := (lintegral_sub_right_eq_self
      (fun x : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) x‖) y).trans
        (kernel_derivative_lintegral hε)

lemma reflected_derivative_kernel_row_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      (measurePreserving_wallReflection Q i).lintegral_comp
        (ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
          (measurable_const.sub measurable_id)))
    _ = _ := (lintegral_sub_left_eq_self
      (fun y : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) y‖) x).trans
        (kernel_derivative_lintegral hε)

lemma reflected_derivative_kernel_col_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := derivative_kernel_col_bound Q hε _

lemma smulRight_stronglyMeasurable {α : Type uAlpha} [MeasurableSpace α]
    {a : α → (ℂ →L[ℝ] ℝ)} {b : α → ℂ} (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) :
    StronglyMeasurable (fun x => (a x).smulRight (b x)) := by
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp_stronglyMeasurable ha).prodMk hb)

lemma directGradS_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (directGradS Q ε f) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y, z.1.2), z.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.fst.sub measurable_snd)).stronglyMeasurable)
      (hf.comp_measurable ((measurable_snd.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd))
  exact h.integral_prod_right

lemma reflectedGradS_stronglyMeasurable (Q : Triangle) (i : Fin 3) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedGradS Q i ε f) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      (fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)).smulRight
        (f ((y, reflectedDirection Q i z.1.2), z.2 + 1)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.fst.sub
          ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd))).stronglyMeasurable)
      (hf.comp_measurable
        ((measurable_snd.prodMk ((measurePreserving_reflectedDirection Q i).measurable.comp
          measurable_fst.fst.snd)).prodMk (measurable_fst.snd.add_const 1)))
  exact h.integral_prod_right

lemma reflectedSmoothingGradient_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedSmoothingGradient Q ε f) :=
  (directGradS_stronglyMeasurable Q ε hf).add
    (Finset.stronglyMeasurable_sum _ (fun i _ => reflectedGradS_stronglyMeasurable Q i ε hf))

lemma eLpNorm_two_le_of_lintegral {α : Type uAlpha} {E : Type uE} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure α)
    {f : α → E} {g : α → F} {C : ℝ≥0∞}
    (h : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) ≤ C * C * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) :
    eLpNorm' f 2 μ ≤ C * eLpNorm' g 2 μ := by
  simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_two]
  calc
    _ ≤ (C * C * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      congr 1
      rw [← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num

lemma directGradS_l2sq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖directGradS Q ε f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ENNReal.ofReal (derivativeMass / ε) * ENNReal.ofReal (derivativeMass / ε) *
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  rw [double_lintegral_assoc, double_lintegral_assoc]
  rw [← mul_assoc _ ((volume Q.table)⁻¹), mul_comm _ ((volume Q.table)⁻¹), mul_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖)) :=
    ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
      (measurable_fst.sub measurable_snd))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        (fderiv ℝ (kernel ε) (p.1 - y)).smulRight (f ((y, p.2.1), p.2.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.sub measurable_snd)).stronglyMeasurable)
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hf.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (derivative_kernel_row_bound Q hε) (derivative_kernel_col_bound Q hε) hFm (fun x c y => by
      rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      simp only [ofReal_norm, Function.comp_apply]
      exact le_rfl)
  exact h

lemma reflectedGradS_l2sq (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖reflectedGradS Q i ε f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ENNReal.ofReal (derivativeMass / ε) * ENNReal.ofReal (derivativeMass / ε) *
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  let g : SmoothPhase → ℂ := fun z => f ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)
  have hg : StronglyMeasurable g := hf.comp_measurable
    (measurePreserving_directionParityReflection Q i).measurable
  have he : (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q) =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q :=
    (measurePreserving_directionParityReflection Q i).lintegral_comp (hf.enorm.pow_const 2)
  rw [← he, double_lintegral_assoc, double_lintegral_assoc]
  rw [← mul_assoc _ ((volume Q.table)⁻¹), mul_comm _ ((volume Q.table)⁻¹), mul_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖)) :=
    ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
      (measurable_fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd)))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        (fderiv ℝ (kernel ε) (p.1 - wallReflection Q i y)).smulRight (g ((y, p.2.1), p.2.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp
          measurable_snd))).stronglyMeasurable)
      (hg.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hg.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (reflected_derivative_kernel_row_bound Q i hε) (reflected_derivative_kernel_col_bound Q i hε)
    hFm (fun x c y => by
      rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      simp only [ofReal_norm, Function.comp_apply]
      exact le_rfl)
  exact h

lemma directGradS_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (directGradS Q ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (directGradS_stronglyMeasurable Q ε hf).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable, ENNReal.toReal_ofNat]
    using eLpNorm_two_le_of_lintegral _ (directGradS_l2sq Q hε hf)

lemma reflectedGradS_eLpNorm (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedGradS Q i ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (reflectedGradS_stronglyMeasurable Q i ε hf).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable, ENNReal.toReal_ofNat]
    using eLpNorm_two_le_of_lintegral _ (reflectedGradS_l2sq Q i hε hf)

lemma eLpNorm_add_sum_fin_three_le {α : Type uAlpha} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] (μ : Measure α) {d : α → E} {r : Fin 3 → α → E}
    {C : ℝ≥0∞} (hd : AEStronglyMeasurable d μ)
    (hr : ∀ i, AEStronglyMeasurable (r i) μ)
    (hdb : eLpNorm d 2 μ ≤ C) (hrb : ∀ i, eLpNorm (r i) 2 μ ≤ C) :
    eLpNorm (d + ∑ i, r i) 2 μ ≤ 4 * C := by
  have hsum := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hr i)
  calc
    _ ≤ eLpNorm d 2 μ + eLpNorm (∑ i, r i) 2 μ := by
      simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hd.add hsum),
        eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hd,
        eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hsum, ENNReal.toReal_ofNat]
        using eLpNorm'_add_le hd hsum (by norm_num : (1 : ℝ) ≤ 2)
    _ ≤ C + ∑ i : Fin 3, eLpNorm (r i) 2 μ :=
      add_le_add hdb (eLpNorm_sum_le (by norm_num))
    _ ≤ C + ∑ _i : Fin 3, C := add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hrb i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma reflectedSmoothingGradient_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      4 * ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  have hd : AEStronglyMeasurable (directGradS Q ε f) (doubleMeasure Q) :=
    (directGradS_stronglyMeasurable Q ε hf).aestronglyMeasurable
  have hr (i : Fin 3) : AEStronglyMeasurable (reflectedGradS Q i ε f) (doubleMeasure Q) :=
    (reflectedGradS_stronglyMeasurable Q i ε hf).aestronglyMeasurable
  have h := eLpNorm_add_sum_fin_three_le (doubleMeasure Q) hd hr
    (directGradS_eLpNorm Q hε hf) (fun i => reflectedGradS_eLpNorm Q i hε hf)
  exact h.trans_eq (mul_assoc _ _ _).symm

lemma reflectedSmoothingGradient_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) := by
  exact (reflectedSmoothingGradient_eLpNorm Q hε hf).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hf₂.eLpNorm_lt_top)

end TriangularBilliards

end
end
end

end OAI
