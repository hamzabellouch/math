import OAI.Analysis.StrictMeans.Eigenmeasure

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma compactTest_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) :
    Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def probabilityFunctional (μ : ProbabilityMeasure X) : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (compactTest_integrable _ f) (compactTest_integrable _ g)
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (μ : Measure X)) (Filter.Eventually.of_forall f.norm_coe_le_norm))

@[simp] lemma probabilityFunctional_apply (μ : ProbabilityMeasure X) (f : C(X, ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂(μ : Measure X) := rfl

lemma probabilityFunctional_monotone (μ : ProbabilityMeasure X) : Monotone (probabilityFunctional μ) :=
  fun f g h => integral_mono (compactTest_integrable _ f) (compactTest_integrable _ g) h

@[simp] lemma probabilityFunctional_one (μ : ProbabilityMeasure X) : probabilityFunctional μ 1 = 1 := by
  simp [probabilityFunctional]

lemma eigenfunctional_power {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (Λ : E →L[ℝ] ℝ) (ρ : ℝ)
    (h : ∀ f, Λ (L f) = ρ * Λ f) (n : ℕ) (f : E) :
    Λ ((L ^ n) f) = ρ ^ n * Λ f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, h, ih, pow_succ]; ring

instance diskFamilyMeasurableSpace : MeasurableSpace DiskFamily := borel _
instance : BorelSpace DiskFamily := ⟨rfl⟩

def dyadicLogGrowth : ℝ := logNormGrowth dyadicOperator dyadicOperator_pow_norm_ge_one
def dyadicRadius : ℝ := Real.exp dyadicLogGrowth
def dyadicExponent : ℝ := dyadicLogGrowth / Real.log 2

lemma dyadicRadius_pos : 0 < dyadicRadius := Real.exp_pos _
lemma dyadicLogGrowth_nonneg : 0 ≤ dyadicLogGrowth :=
  logNormGrowth_nonneg _ _
lemma dyadicExponent_nonneg : 0 ≤ dyadicExponent :=
  div_nonneg dyadicLogGrowth_nonneg (Real.log_nonneg (by norm_num))

theorem exists_dyadic_eigenfunctional :
    ∃ Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ, Monotone Λ ∧ Λ 1 = 1 ∧
      ∀ φ : C(DiskFamily, ℝ), Λ (dyadicOperator φ) = dyadicRadius * Λ φ := by
  obtain ⟨μ, hμ⟩ := exists_exact_eigenprobability dyadicOperator
    dyadicOperator_monotone dyadicOperator_pow_norm_ge_one
  exact ⟨probabilityFunctional μ, probabilityFunctional_monotone μ,
    probabilityFunctional_one μ, hμ⟩

lemma eigenfunctional_horizontal_period (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (ρ : ℝ) (hρ : 1 < ρ)
    (hΛ : ∀ φ : C(DiskFamily, ℝ), Λ (dyadicOperator φ) = ρ * Λ φ) :
    ∀ φ : C(DiskFamily, ℝ), Λ (affineOperator (horizontalPoint 2) φ) = Λ φ := by
  intro φ
  let d := |Λ (affineOperator (horizontalPoint 2) φ) - Λ φ|
  have hp (n : ℕ) : ρ ^ n * d ≤ ‖Λ‖ * (128 * ‖φ‖) := by
    have he : ρ ^ n * (Λ (affineOperator (horizontalPoint 2) φ) - Λ φ) =
        Λ ((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ) := by
      rw [sub_apply, mul_apply_eq_comp, map_sub,
        eigenfunctional_power dyadicOperator Λ ρ hΛ n,
        eigenfunctional_power dyadicOperator Λ ρ hΛ n]
      ring
    calc
      ρ ^ n * d = |ρ ^ n * (Λ (affineOperator (horizontalPoint 2) φ) - Λ φ)| := by
        rw [abs_mul, abs_of_pos (pow_pos (lt_trans zero_lt_one hρ) n)]
      _ = ‖Λ ((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ)‖ :=
        congrArg abs he
      _ ≤ ‖Λ‖ * ‖(dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ‖ := Λ.le_opNorm _
      _ ≤ ‖Λ‖ * (128 * ‖φ‖) := mul_le_mul_of_nonneg_left
        (((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n).le_opNorm φ).trans
          (mul_le_mul_of_nonneg_right (dyadic_shift_norm_le n) (norm_nonneg φ))) (norm_nonneg Λ)
  have hb (n : ℕ) : d ≤ (ρ ^ n)⁻¹ * (‖Λ‖ * (128 * ‖φ‖)) := by
    apply (le_inv_mul_iff₀ (pow_pos (lt_trans zero_lt_one hρ) n)).mpr
    exact hp n
  have ht := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hρ)).mul_const
    (‖Λ‖ * (128 * ‖φ‖))
  have hd : d ≤ 0 := by simpa only [zero_mul] using ge_of_tendsto' ht hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hd)

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_xyPoint {x y : ℝ → ℝ} (hx : Continuous x) (hy : Continuous y)
    (hp : ∀ t, 0 < y t) : Continuous (fun t => xyPoint (x t) (y t) (hp t)) :=
  ((Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul_const Complex.I)).upperHalfPlaneMk _

lemma continuous_horizontalPoint : Continuous horizontalPoint :=
  continuous_xyPoint continuous_id continuous_const _

lemma affineProduct_horizontal (x s : ℝ) :
    affineProduct (horizontalPoint x) (horizontalPoint s) = horizontalPoint (x + s) := by
  simp [horizontalPoint, affineProduct_xyPoint]

lemma affineProduct_horizontal_xy (x s t : ℝ) (ht : 0 < t) :
    affineProduct (horizontalPoint x) (xyPoint s t ht) = xyPoint (x + s) t ht := by
  simp [horizontalPoint, affineProduct_xyPoint]

lemma affineProduct_xy_horizontal (x y s : ℝ) (hy : 0 < y) :
    affineProduct (xyPoint x y hy) (horizontalPoint s) = xyPoint (x + y * s) y hy := by
  simp [horizontalPoint, affineProduct_xyPoint]

lemma continuous_functional_affine (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (φ : C(DiskFamily, ℝ)) :
    Continuous (fun z => Λ (affineOperator z φ)) :=
  Λ.continuous.comp (continuous_affineOperator_strong φ)

lemma affineOperator_compact_bound (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b, ‖affineOperator (z t)‖ ≤ C := by
  let Y := (uIcc a b) × DiskFamily
  let : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  let W : C(Y, ℝ) := ⟨fun p => ‖halfPlaneQ p.2 (z p.1)‖,
    (continuous_halfPlaneQ.comp (continuous_snd.prodMk
      (hz.comp (continuous_subtype_val.comp continuous_fst)))).norm⟩
  refine ⟨‖W‖, norm_nonneg _, fun t ht => affineOperator_norm_bound (norm_nonneg _) ?_⟩
  intro f
  simpa only [W, ContinuousMap.coe_mk, norm_norm] using W.norm_coe_le_norm (⟨t, ht⟩, f)

section WeakIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : E →L[ℝ] ℝ) (A : ℝ → E →L[ℝ] E)
  (hA : ∀ f : E, Continuous (fun t => A t f)) (a b : ℝ)
  (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b, ‖A t‖ ≤ C)

def intervalFunctional : E →L[ℝ] ℝ :=
  let C := hbound.choose
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add
          ((Λ.continuous.comp (hA f)).intervalIntegrable _ _)
          ((Λ.continuous.comp (hA g)).intervalIntegrable _ _)
      map_smul' := fun c f => by
        simp only [map_smul]
        exact intervalIntegral.integral_smul c _ }
    (‖Λ‖ * C * |b - a|) (fun f => by
      have hb := hbound.choose_spec
      calc
        ‖∫ t in a..b, Λ (A t f)‖ ≤ (‖Λ‖ * (C * ‖f‖)) * |b - a| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          exact (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (((A t).le_opNorm f).trans
              (mul_le_mul_of_nonneg_right (hb.2 t (uIoc_subset_uIcc ht)) (norm_nonneg f)))
            (norm_nonneg Λ))
        _ = (‖Λ‖ * C * |b - a|) * ‖f‖ := by ring)

@[simp] lemma intervalFunctional_apply (f : E) :
    intervalFunctional Λ A hA a b hbound f = ∫ t in a..b, Λ (A t f) := rfl
end WeakIntegral

def affineIntervalFunctional (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  intervalFunctional Λ (fun t => affineOperator (z t))
    (fun φ => (continuous_affineOperator_strong φ).comp hz) a b
    (affineOperator_compact_bound z hz a b)

@[simp] lemma affineIntervalFunctional_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) (φ : C(DiskFamily, ℝ)) :
    affineIntervalFunctional Λ z hz a b φ = ∫ t in a..b, Λ (affineOperator (z t) φ) := rfl

def horizontalAverage (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • affineIntervalFunctional Λ horizontalPoint continuous_horizontalPoint 0 2

@[simp] lemma horizontalAverage_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ φ = (1 / 2 : ℝ) * ∫ t in 0..2, Λ (affineOperator (horizontalPoint t) φ) := rfl

lemma functional_horizontal_periodic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (y : ℝ) (hy : 0 < y) (φ : C(DiskFamily, ℝ)) :
    Periodic (fun x => Λ (affineOperator (xyPoint x y hy) φ)) 2 := by
  intro x
  change Λ (affineOperator (xyPoint (x + 2) y hy) φ) = Λ (affineOperator (xyPoint x y hy) φ)
  have he : xyPoint (x + 2) y hy = affineProduct (horizontalPoint 2) (xyPoint x y hy) := by
    rw [affineProduct_horizontal_xy, add_comm]
  rw [he, ← affineOperator_mul, mul_apply_eq_comp, hΛ]

lemma horizontalAverage_invariant (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (s : ℝ) (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (affineOperator (horizontalPoint s) φ) = horizontalAverage Λ φ := by
  simp only [horizontalAverage_apply]
  have he (x : ℝ) : affineOperator (horizontalPoint x) (affineOperator (horizontalPoint s) φ) =
      affineOperator (horizontalPoint (x + s)) φ := by
    rw [← mul_apply_eq_comp, affineOperator_mul, affineProduct_horizontal]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (affineOperator (horizontalPoint x) φ)) s]
  have hp : Periodic (fun x => Λ (affineOperator (horizontalPoint x) φ)) 2 :=
    functional_horizontal_periodic Λ hΛ 1 zero_lt_one φ
  rw [show 0 + s = s by ring, show (2 : ℝ) + s = s + 2 by ring]
  rw [hp.intervalIntegral_add_eq s 0]
  simp only [zero_add]

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def halfScalePoint : UpperHalfPlane := xyPoint 0 (1 / 2) (by norm_num)

lemma dyadicLeft_eq_horizontal_scale :
    dyadicLeft = affineProduct (horizontalPoint (-1 / 2)) halfScalePoint := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, horizontalPoint, halfScalePoint, xyPoint]
  ring

lemma dyadicRight_eq_horizontal_scale :
    dyadicRight = affineProduct (horizontalPoint (1 / 2)) halfScalePoint := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, horizontalPoint, halfScalePoint, xyPoint]
  ring

lemma horizontal_dyadicLeft (x : ℝ) :
    affineProduct (horizontalPoint x) dyadicLeft =
      affineProduct dyadicLeft (horizontalPoint (2 * x)) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, horizontalPoint, xyPoint]
  ring

lemma horizontal_dyadicRight (x : ℝ) :
    affineProduct (horizontalPoint x) dyadicRight =
      affineProduct dyadicRight (horizontalPoint (2 * x)) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, horizontalPoint, xyPoint]
  ring

lemma affineOperator_horizontal_dyadic (x : ℝ) :
    affineOperator (horizontalPoint x) * dyadicOperator =
      dyadicOperator * affineOperator (horizontalPoint (2 * x)) := by
  rw [dyadicOperator, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    affineOperator_mul, affineOperator_mul, affineOperator_mul, affineOperator_mul,
    horizontal_dyadicLeft, horizontal_dyadicRight]

lemma periodic_integral_double {g : ℝ → ℝ} (hg : Continuous g) (hp : Periodic g 2) :
    (∫ x in (0 : ℝ)..2, g (2 * x)) = ∫ x in (0 : ℝ)..2, g x := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num only [mul_zero, show (2 : ℝ) * 2 = 4 by norm_num, smul_eq_mul]
  have he : (∫ x in (2 : ℝ)..4, g x) = ∫ x in (0 : ℝ)..2, g x := by
    convert hp.intervalIntegral_add_eq 2 0 using 1 <;> norm_num
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (0 : ℝ) 2) (hg.intervalIntegrable (2 : ℝ) 4)
  rw [← hh, he]
  ring

lemma horizontalAverage_eigen (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hperiod : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (heigen : ∀ φ, Λ (dyadicOperator φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (dyadicOperator φ) = ρ * horizontalAverage Λ φ := by
  have he (x : ℝ) : Λ (affineOperator (horizontalPoint x) (dyadicOperator φ)) =
      ρ * Λ (affineOperator (horizontalPoint (2 * x)) φ) := by
    rw [← mul_apply_eq_comp, affineOperator_horizontal_dyadic, mul_apply_eq_comp, heigen]
  simp only [horizontalAverage_apply]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hp : Periodic (fun x => Λ (affineOperator (horizontalPoint x) φ)) 2 :=
    functional_horizontal_periodic Λ hperiod 1 zero_lt_one φ
  have hg : Continuous (fun x => Λ (affineOperator (horizontalPoint x) φ)) :=
    (continuous_functional_affine Λ φ).comp continuous_horizontalPoint
  rw [periodic_integral_double hg hp]
  ring

lemma horizontally_invariant_dyadic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (φ : C(DiskFamily, ℝ)) : Λ (dyadicOperator φ) = Λ (affineOperator halfScalePoint φ) := by
  change Λ ((1 / 2 : ℝ) • (affineOperator dyadicLeft φ + affineOperator dyadicRight φ)) = _
  rw [map_smul, map_add, dyadicLeft_eq_horizontal_scale, dyadicRight_eq_horizontal_scale,
    ← affineOperator_mul, ← affineOperator_mul, mul_apply_eq_comp, mul_apply_eq_comp, hΛ, hΛ]
  simp only [smul_eq_mul]
  ring

lemma horizontalAverage_halfScale (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hperiod : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (heigen : ∀ φ, Λ (dyadicOperator φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (affineOperator halfScalePoint φ) = ρ * horizontalAverage Λ φ := by
  rw [← horizontally_invariant_dyadic (horizontalAverage Λ)
    (horizontalAverage_invariant Λ hperiod)]
  exact horizontalAverage_eigen Λ ρ hperiod heigen φ

end
end StrictInverseFirstPower

end

end OAI
