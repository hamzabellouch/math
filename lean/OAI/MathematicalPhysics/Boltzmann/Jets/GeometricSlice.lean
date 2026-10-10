import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyConvex
import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseAverage
import OAI.MathematicalPhysics.Boltzmann.Collision.WeightAlgebra
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-!
# Degenerate slices and nonnegative singular integrals

The line integral through the velocity axis is infinite. Its exceptional transverse
parameters form an affine line of two-dimensional measure zero. These results keep
that extended value explicit and justify the almost-everywhere scalar estimates,
including products with arbitrary axial probability measures.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GaussianDiskMixture
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness.GeometricSlice

/-- Signed distance of the transverse collision line from the velocity axis. -/
def sliceOffset (v p : Transverse) : ℝ := inner ℝ (direction (v - p)) v

theorem measurable_sliceOffset (v : Transverse) : Measurable (sliceOffset v) := by
  unfold sliceOffset direction
  fun_prop

def RegularTransverse (v p : Transverse) : Prop :=
  v - p ≠ 0 ∧ sliceOffset v p ≠ 0

theorem sliceOffset_eq_zero_iff (v p : Transverse) :
    sliceOffset v p = 0 ↔ inner ℝ v p = ‖v‖ ^ 2 := by
  by_cases hn : v - p = 0
  · have hp : p = v := (sub_eq_zero.mp hn).symm
    subst p
    simp [sliceOffset, direction]
  · have hnorm : ‖v - p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
    rw [sliceOffset, direction, real_inner_smul_left, mul_eq_zero]
    simp only [inv_eq_zero, hnorm, false_or]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm p v]
    constructor <;> intro h <;> linarith

theorem regularTransverse_iff (v p : Transverse) :
    RegularTransverse v p ↔ inner ℝ v p ≠ ‖v‖ ^ 2 := by
  constructor
  · intro h
    exact mt (sliceOffset_eq_zero_iff v p).mpr h.2
  · intro h
    have hs : sliceOffset v p ≠ 0 := mt (sliceOffset_eq_zero_iff v p).mp h
    refine ⟨?_, hs⟩
    intro hn
    apply hs
    simp [sliceOffset, direction, hn]

theorem measurableSet_regularTransverse (v : Transverse) :
    MeasurableSet {p | RegularTransverse v p} := by
  simp_rw [regularTransverse_iff]
  exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl

/-- The bad transverse parameters lie in a proper affine hyperplane. -/
theorem volume_sliceOffset_zero {v : Transverse} (hv : v ≠ 0) :
    volume {p | sliceOffset v p = 0} = 0 := by
  let K : Submodule ℝ Transverse := (innerSL ℝ v).ker
  let S : AffineSubspace ℝ Transverse := AffineSubspace.mk' v K
  have hset : {p | sliceOffset v p = 0} = (S : Set Transverse) := by
    ext p
    rw [mem_ofPred_eq, sliceOffset_eq_zero_iff]
    change inner ℝ v p = ‖v‖ ^ 2 ↔ inner ℝ v (p - v) = 0
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero]
  have hproper : S ≠ ⊤ := by
    intro hs
    have hm : (0 : Transverse) ∈ S := by rw [hs]; trivial
    change inner ℝ v (0 - v) = 0 at hm
    simp only [zero_sub, inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq,
      sq_eq_zero_iff, norm_eq_zero] at hm
    exact hv hm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem ae_regularTransverse_volume {v : Transverse} (hv : v ≠ 0) :
    ∀ᵐ p ∂volume, RegularTransverse v p := by
  have hs : ∀ᵐ p ∂volume, sliceOffset v p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_sliceOffset_zero hv
  filter_upwards [hs] with p hp
  refine ⟨?_, hp⟩
  intro hn
  apply hp
  simp [sliceOffset, direction, hn]

theorem regularTransverse_zero {v : Transverse} (hv : v ≠ 0) :
    RegularTransverse v 0 := by
  rw [regularTransverse_iff, inner_zero_right]
  exact Ne.symm (ne_of_gt (pow_pos (norm_pos_iff.mpr hv) 2))

theorem ae_regularTransverse_atom {v : Transverse} (hv : v ≠ 0) :
    ∀ᵐ p ∂Measure.dirac (0 : Transverse), RegularTransverse v p := by
  rw [ae_dirac_eq]
  exact regularTransverse_zero hv

theorem ae_regularTransverse_uniformDisk {v : Transverse} (hv : v ≠ 0) (d : ℝ) :
    ∀ᵐ p ∂uniformDiskLaw d, RegularTransverse v p :=
  (withDensity_absolutelyContinuous volume _).ae_le (ae_regularTransverse_volume hv)

theorem ae_regularTransverse_gaussian {v : Transverse} (hv : v ≠ 0) (d : ℝ) :
    ∀ᵐ p ∂gaussianLaw d, RegularTransverse v p :=
  (withDensity_absolutelyContinuous volume _).ae_le (ae_regularTransverse_volume hv)

/-- No regularity of the axial law is needed to preserve the exceptional null set. -/
theorem ae_regularTransverse_prod {v : Transverse} {μ : Measure Transverse}
    {ρ : Measure ℝ} [SFinite ρ] (hμ : ∀ᵐ p ∂μ, RegularTransverse v p) :
    ∀ᵐ p ∂μ.prod ρ, RegularTransverse v p.1 := by
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_regularTransverse v).preimage measurable_fst)).mpr
  filter_upwards [hμ] with p hp
  exact ae_of_all _ (fun _ => hp)

/-- The scalar line singularity retains its infinite value on a zero-distance slice. -/
def extendedPower (q x : ℝ) : ℝ≥0∞ :=
  if x = 0 then ∞ else ENNReal.ofReal (|x| ^ (1 - q))

theorem measurable_extendedPower (q : ℝ) : Measurable (extendedPower q) := by
  unfold extendedPower
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  exact (measurable_abs.pow measurable_const).ennreal_ofReal

theorem extendedPower_ae_eq {A : ℝ} (hA : A ≠ 0) (B q : ℝ) :
    (fun x : ℝ => extendedPower q (A - B * x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (|A - B * x| ^ (1 - q))) := by
  by_cases hB : B = 0
  · exact ae_of_all _ (fun x => by simp [extendedPower, hB, hA])
  · have hz : ∀ᵐ x ∂volume, x ≠ A / B := volume.ae_ne (A / B)
    filter_upwards [hz] with x hx
    have hAx : A - B * x ≠ 0 := by
      intro heq
      apply hx
      apply (eq_div_iff hB).mpr
      nlinarith [sub_eq_zero.mp heq]
    simp only [extendedPower, hAx, ↓reduceIte]

/-- The extended-valued scalar integral has the same finite bound as the ordinary
integral whenever the nonzero intercept excludes an identically singular slice. -/
theorem lintegral_extendedPower_interval_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫⁻ x in Ioc a b, extendedPower q (A - B * x)) ≤
      ENNReal.ofReal (AxialSlices.scalarConstant (1 - q) *
        (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q))) := by
  have hi := AxialSlices.intervalIntegrable_abs_affine_rpow
    (show -1 < 1 - q by linarith) A B a b
  rw [lintegral_congr_ae (ae_restrict_of_ae (extendedPower_ae_eq hA B q))]
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
  rw [← intervalIntegral.integral_of_le hab.le]
  exact ENNReal.ofReal_le_ofReal (AxialSlices.scalar_interval_bound hq₁ hq₂ hab hR ha hb hA)

/-- Extended expectation kernel, infinite on degenerate transverse slices. -/
def extendedKernel (q : ℝ) (v p : Transverse) : ℝ≥0∞ := by
  classical
  exact if RegularTransverse v p then ENNReal.ofReal (kernel q (direction v) (v - p)) else ∞

theorem measurable_extendedKernel (q : ℝ) (v : Transverse) :
    Measurable (extendedKernel q v) := by
  classical
  unfold extendedKernel
  apply Measurable.ite (measurableSet_regularTransverse v) _ measurable_const
  unfold kernel
  fun_prop

theorem extendedKernel_ae_eq {v : Transverse} {μ : Measure Transverse}
    (hμ : ∀ᵐ p ∂μ, RegularTransverse v p) (q : ℝ) :
    extendedKernel q v =ᵐ[μ] fun p => ENNReal.ofReal (kernel q (direction v) (v - p)) := by
  filter_upwards [hμ] with p hp
  simp only [extendedKernel, hp, ↓reduceIte]

theorem uniformDisk_extendedKernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂uniformDiskLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_uniformDisk hv d) q)]
  have hm : Measurable (fun p => ENNReal.ofReal (kernel q (direction v) (v - p))) := by
    unfold kernel
    fun_prop
  rw [uniformDiskLaw_lintegral hd _ hm]
  have hi := integrableOn_kernel_translatedDisk hq₂ hd (direction v) (norm_direction hv) v
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun p => kernel_nonneg q (direction v) (v - p)))]
  rw [mul_comm, ← div_eq_mul_inv]
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi * d ^ 2)]
  exact ENNReal.ofReal_le_ofReal (uniformDisk_expectation_le hq₁ hq₂ hd hv)

theorem atom_extendedKernel_lintegral_le (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂Measure.dirac (0 : Transverse)) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_atom hv) q),
    lintegral_dirac]
  simpa only [integral_dirac, sub_zero] using ENNReal.ofReal_le_ofReal (atomZero_expectation_le q hv)

theorem gaussian_extendedKernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂gaussianLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_gaussian hv d) q)]
  exact gaussianLaw_kernel_lintegral_le hq₁ hq₂ hd hv

/-- The line estimate with its correct extended value at zero distance. -/
theorem lintegral_lineWeight_le_extended {q R : ℝ} (hq : 1 < q) (hR : 0 ≤ R)
    (e : Transverse) (he : ‖e‖ = 1) (D m : ℝ) :
    (∫⁻ s in Icc (m - R) (m + R),
      ENNReal.ofReal (TransverseLine.lineWeight q e D s)) ≤
      ENNReal.ofReal (2 * R) + ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q D := by
  have hc := AxialSlices.lineConstant_pos hq
  by_cases hD : D = 0
  · rw [extendedPower, ite_eq_left hD, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc)),
      add_top]
    exact le_top
  · rw [extendedPower, ite_eq_right hD, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact TransverseLine.lintegral_lineWeight_le hq hD hR e he m

/-- Integration over the coordinate rectangle; this is an explicit upper bound,
not a definition of the original ball restriction. -/
def rectangleLineMass (q : ℝ) (e : Transverse) (A B m R a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioc a b, ∫⁻ s in Icc (m - R) (m + R),
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)

theorem rectangleLineMass_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    rectangleLineMass q e A B m R a b ≤
      ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
        (AxialSlices.scalarConstant (1 - q) *
          (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)))) := by
  have hc := (AxialSlices.lineConstant_pos hq₁).le
  have hs := lintegral_extendedPower_interval_le hq₁ hq₂ hab hR ha hb hA (B := B)
  unfold rectangleLineMass
  calc
    _ ≤ ∫⁻ z in Ioc a b, ENNReal.ofReal (2 * R) +
        ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q (A - B * z) :=
      lintegral_mono (fun z => lintegral_lineWeight_le_extended hq₁ hR.le e he _ m)
    _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ∫⁻ z in Ioc a b, extendedPower q (A - B * z) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    _ ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ENNReal.ofReal (AxialSlices.scalarConstant (1 - q) *
            (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q))) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
        ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by
          apply mul_nonneg hc
          apply mul_nonneg (AxialSlices.scalarConstant_pos (by linarith)).le
          positivity)]

/-- The ball restriction in transverse-line and axial-displacement coordinates. -/
def ballLineRegion (e v : Transverse) (D z R : ℝ) : Set ℝ :=
  {s | ‖TransverseLine.line e D s - v‖ ^ 2 + z ^ 2 ≤ R ^ 2}

def ballLineMass (q : ℝ) (e v : Transverse) (A B R a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioc a b, ∫⁻ s in ballLineRegion e v (A - B * z) z R,
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)

theorem inner_quarterTurn_line_sub (e v : Transverse) (he : ‖e‖ = 1) (D s : ℝ) :
    inner ℝ (TransverseLine.quarterTurn e) (TransverseLine.line e D s - v) =
      s - inner ℝ (TransverseLine.quarterTurn e) v := by
  have ho : inner ℝ (TransverseLine.quarterTurn e) e = 0 := by
    rw [real_inner_comm, TransverseLine.inner_quarterTurn]
  rw [inner_sub_right]
  simp only [TransverseLine.line, inner_add_right, inner_smul_right, ho,
    real_inner_self_eq_norm_sq, TransverseLine.norm_quarterTurn, he]
  ring

theorem ballLineRegion_subset_rectangle {R : ℝ} (hR : 0 ≤ R)
    (e v : Transverse) (he : ‖e‖ = 1) (D z : ℝ) :
    ballLineRegion e v D z R ⊆
      Icc (inner ℝ (TransverseLine.quarterTurn e) v - R)
        (inner ℝ (TransverseLine.quarterTurn e) v + R) := by
  intro s hs
  have hnorm : ‖TransverseLine.line e D s - v‖ ≤ R := by
    change ‖TransverseLine.line e D s - v‖ ^ 2 + z ^ 2 ≤ R ^ 2 at hs
    nlinarith [sq_nonneg z, norm_nonneg (TransverseLine.line e D s - v)]
  have hi := abs_real_inner_le_norm (TransverseLine.quarterTurn e)
    (TransverseLine.line e D s - v)
  rw [inner_quarterTurn_line_sub e v he, TransverseLine.norm_quarterTurn, he, one_mul] at hi
  have ha := abs_le.mp (hi.trans hnorm)
  constructor <;> linarith [ha.1, ha.2]

theorem ballLineMass_le_rectangle {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (e v : Transverse) (he : ‖e‖ = 1) (A B a b : ℝ) :
    ballLineMass q e v A B R a b ≤
      rectangleLineMass q e A B (inner ℝ (TransverseLine.quarterTurn e) v) R a b := by
  apply lintegral_mono
  intro z
  exact lintegral_mono_set (ballLineRegion_subset_rectangle hR e v he (A - B * z) z)

theorem ballLineMass_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (e v : Transverse) (he : ‖e‖ = 1) :
    ballLineMass q e v A B R a b ≤
      ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
        (AxialSlices.scalarConstant (1 - q) *
          (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)))) :=
  (ballLineMass_le_rectangle hR.le q e v he A B a b).trans
    (rectangleLineMass_le hq₁ hq₂ hab hR ha hb hA e he _)

def transverseWeight (q : ℝ) (v : Transverse) : ℝ := 1 + ‖v‖ ^ (-q)

def intervalCoefficient (q R ell : ℝ) : ℝ :=
  AxialSlices.lineConstant q * (AxialSlices.scalarConstant (1 - q) *
    (R ^ (q - 1) * ell ^ (2 - q)))

def averagingCoefficient (q R ell r : ℝ) : ℝ :=
  (2 * R * ell + intervalCoefficient q R ell * r ^ (1 - q)) / (1 + r ^ (-q))

theorem transverseWeight_pos (q : ℝ) (v : Transverse) : 0 < transverseWeight q v := by
  unfold transverseWeight
  positivity

theorem intervalCoefficient_pos {q R ell : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (hell : 0 < ell) : 0 < intervalCoefficient q R ell := by
  unfold intervalCoefficient
  exact mul_pos (AxialSlices.lineConstant_pos hq₁)
    (mul_pos (AxialSlices.scalarConstant_pos (by linarith))
      (mul_pos (Real.rpow_pos_of_pos hR _) (Real.rpow_pos_of_pos hell _)))

theorem averagingCoefficient_pos {q R ell r : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (hell : 0 < ell) (hr : 0 ≤ r) : 0 < averagingCoefficient q R ell r := by
  have hc := intervalCoefficient_pos hq₁ hq₂ hR hell
  unfold averagingCoefficient
  positivity

theorem sliceOffset_eq_norm_mul_angle {v : Transverse} (hv : v ≠ 0) (p : Transverse) :
    sliceOffset v p = ‖v‖ * inner ℝ (direction v) (direction (v - p)) := by
  have he : inner ℝ (direction v) (direction (v - p)) = ‖v‖⁻¹ * sliceOffset v p := by
    change inner ℝ (‖v‖⁻¹ • v) (direction (v - p)) = _
    rw [real_inner_smul_left]
    unfold sliceOffset
    congr 1
    exact real_inner_comm _ _
  rw [he, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_mul]

theorem sliceOffset_rpow {v : Transverse} (hv : v ≠ 0) (p : Transverse) (q : ℝ) :
    |sliceOffset v p| ^ (1 - q) = ‖v‖ ^ (1 - q) *
      |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) := by
  rw [sliceOffset_eq_norm_mul_angle hv, abs_mul, abs_of_nonneg (norm_nonneg v),
    Real.mul_rpow (norm_nonneg v) (abs_nonneg _)]

private theorem normalized_sum_bound {u w t beta c n : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (ht : 0 ≤ t) (hb : 0 ≤ beta)
    (hc : 0 < c) (hn : 0 < n) :
    (u + w * t * beta) / (c * n) ≤ (u + w * t) / c * ((1 + beta) / n) := by
  have hnum : u + w * t * beta ≤ (u + w * t) * (1 + beta) := by
    nlinarith [mul_nonneg hu hb, mul_nonneg hw ht]
  calc
    _ ≤ ((u + w * t) * (1 + beta)) / (c * n) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hc.le hn.le)
    _ = _ := by field_simp

/-- The ball-restricted chart integral with factor `1 / (W(v) * ‖v-p‖)`.
Identifying this chart factor with the collision-plane measure is a separate
change-of-variables statement. Degenerate parameters retain the value infinity. -/
def normalizedBallSlice (q : ℝ) (v : Transverse) (t : ℝ) (p : Transverse)
    (alpha R a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if RegularTransverse v p then
    ENNReal.ofReal (1 / (transverseWeight q v * ‖v - p‖)) *
      ballLineMass q (direction (v - p)) v (sliceOffset v p)
        ((t - alpha) / ‖v - p‖) R a b
  else ∞

private theorem slice_numerator_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) {p : Transverse} (hp : RegularTransverse v p) :
    (2 * R * (b - a) + AxialSlices.lineConstant q *
      (AxialSlices.scalarConstant (1 - q) *
        (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) /
        (transverseWeight q v * ‖v - p‖) ≤
      averagingCoefficient q R (b - a) ‖v‖ * kernel q (direction v) (v - p) := by
  have hc := (intervalCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab)).le
  have h := normalized_sum_bound (by positivity : 0 ≤ 2 * R * (b - a)) hc
    (Real.rpow_nonneg (norm_nonneg v) (1 - q))
    (Real.rpow_nonneg (abs_nonneg (inner ℝ (direction v) (direction (v - p)))) (1 - q))
    (transverseWeight_pos q v) (norm_pos_iff.mpr hp.1)
  rw [sliceOffset_rpow hv]
  simpa only [averagingCoefficient, intervalCoefficient, transverseWeight, kernel, direction, mul_assoc] using h

/-- A pointwise bound with all singular transverse cases handled in the extended reals. -/
theorem normalizedBallSlice_le {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t alpha : ℝ) (p : Transverse) :
    normalizedBallSlice q v t p alpha R a b ≤
      ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) * extendedKernel q v p := by
  classical
  have hc := averagingCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab) (norm_nonneg v)
  by_cases hp : RegularTransverse v p
  · rw [normalizedBallSlice, ite_eq_left hp, extendedKernel, ite_eq_left hp]
    have hm := ballLineMass_le hq₁ hq₂ hab hR ha hb hp.2
      (direction (v - p)) v (norm_direction hp.1) (B := (t - alpha) / ‖v - p‖)
    have hw := transverseWeight_pos q v
    have hn := norm_pos_iff.mpr hp.1
    calc
      _ ≤ ENNReal.ofReal (1 / (transverseWeight q v * ‖v - p‖)) *
          ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
            (AxialSlices.scalarConstant (1 - q) *
              (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) :=
        mul_le_mul_right hm _
      _ = ENNReal.ofReal ((2 * R * (b - a) + AxialSlices.lineConstant q *
            (AxialSlices.scalarConstant (1 - q) *
              (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) /
              (transverseWeight q v * ‖v - p‖)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖ *
          kernel q (direction v) (v - p)) :=
        ENNReal.ofReal_le_ofReal (slice_numerator_bound hq₁ hq₂ hab hR hv hp)
      _ = _ := ENNReal.ofReal_mul hc.le
  · rw [normalizedBallSlice, ite_eq_right hp, extendedKernel, ite_eq_right hp,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]

theorem measurable_ballLineMass {α : Type*} [MeasurableSpace α]
    (q : ℝ) (v : Transverse) (R a b : ℝ)
    (e : α → Transverse) (A B : α → ℝ)
    (he : Measurable e) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun y => ballLineMass q (e y) v (A y) (B y) R a b) := by
  classical
  have hquarter : Measurable TransverseLine.quarterTurn := by
    unfold TransverseLine.quarterTurn
    fun_prop
  let point : (α × ℝ) × ℝ → Transverse := fun u =>
    TransverseLine.line (e u.1.1) (A u.1.1 - B u.1.1 * u.1.2) u.2
  have hp : Measurable point := by
    dsimp [point]
    unfold TransverseLine.line
    have he' : Measurable (fun u : (α × ℝ) × ℝ => e u.1.1) :=
      he.comp (measurable_fst.comp measurable_fst)
    have hd : Measurable (fun u : (α × ℝ) × ℝ => A u.1.1 - B u.1.1 * u.1.2) := by
      fun_prop
    exact (hd.smul he').add (measurable_snd.smul (hquarter.comp he'))
  let f : (α × ℝ) × ℝ → ℝ≥0∞ := fun u =>
    if ‖point u - v‖ ^ 2 + u.1.2 ^ 2 ≤ R ^ 2 then
      ENNReal.ofReal (1 + ‖point u‖ ^ (-q)) else 0
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop
  have hi := hf.lintegral_prod_right' (ν := volume)
  have hj := hi.lintegral_prod_right' (ν := volume.restrict (Ioc a b))
  have heq : (fun y => ballLineMass q (e y) v (A y) (B y) R a b) =
      fun y => ∫⁻ z in Ioc a b, ∫⁻ s, f ((y, z), s) := by
    funext y
    unfold ballLineMass
    apply lintegral_congr
    intro z
    have hm : MeasurableSet (ballLineRegion (e y) v (A y - B y * z) z R) := by
      unfold ballLineRegion
      apply measurableSet_le
      · unfold TransverseLine.line TransverseLine.quarterTurn
        fun_prop
      · exact measurable_const
    rw [← lintegral_indicator hm]
    rfl
  rw [heq]
  exact hj

theorem measurable_normalizedBallSlice (q : ℝ) (v : Transverse) (t R a b : ℝ) :
    Measurable (fun p : Transverse × ℝ => normalizedBallSlice q v t p.1 p.2 R a b) := by
  classical
  have he : Measurable (fun p : Transverse × ℝ => direction (v - p.1)) := by
    unfold direction
    fun_prop
  have hA : Measurable (fun p : Transverse × ℝ => sliceOffset v p.1) :=
    (measurable_sliceOffset v).comp measurable_fst
  have hB : Measurable (fun p : Transverse × ℝ => (t - p.2) / ‖v - p.1‖) := by fun_prop
  have hm := measurable_ballLineMass q v R a b _ _ _ he hA hB
  have hc : Measurable (fun p : Transverse × ℝ =>
      ENNReal.ofReal (1 / (transverseWeight q v * ‖v - p.1‖))) := by fun_prop
  unfold normalizedBallSlice
  exact Measurable.ite ((measurableSet_regularTransverse v).preimage measurable_fst)
    (hc.mul hm) measurable_const

theorem averagingCoefficient_bound {q R ell r : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 < R) (hell : 0 < ell) (hr : 0 < r) :
    averagingCoefficient q R ell r * (expectationConstant q / r) ≤
      expectationConstant q * (2 * R * ell + intervalCoefficient q R ell) := by
  have hreg := regular_fraction_le_one hr hq₁.le
  have hsing := singular_fraction_le_one hr q
  have hc := (intervalCoefficient_pos hq₁ hq₂ hR hell).le
  have hpow : r ^ (1 - q) * r⁻¹ = r ^ (-q) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = expectationConstant q * (2 * R * ell * (r⁻¹ / (1 + r ^ (-q))) +
        intervalCoefficient q R ell * ((r ^ (1 - q) * r⁻¹) / (1 + r ^ (-q)))) := by
      unfold averagingCoefficient
      ring
    _ = expectationConstant q * (2 * R * ell * (r⁻¹ / (1 + r ^ (-q))) +
        intervalCoefficient q R ell * (r ^ (-q) / (1 + r ^ (-q)))) := by rw [hpow]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (expectationConstant_pos q).le
      have h₁ := mul_le_mul_of_nonneg_left hreg (by positivity : 0 ≤ 2 * R * ell)
      have h₂ := mul_le_mul_of_nonneg_left hsing hc
      nlinarith

/-- Averaging over an arbitrary axial probability leaves the uniform transverse
bound unchanged. The transverse expectation premise is discharged below for each law. -/
theorem normalizedBallSlice_product_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂μ.prod ρ) ≤
      ENNReal.ofReal (expectationConstant q *
        (2 * R * (b - a) + intervalCoefficient q R (b - a))) := by
  have hc := (averagingCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab) (norm_nonneg v)).le
  have hm : Measurable (fun p : Transverse × ℝ => extendedKernel q v p.1) :=
    (measurable_extendedKernel q v).comp measurable_fst
  calc
    _ ≤ ∫⁻ p : Transverse × ℝ,
        ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) * extendedKernel q v p.1 ∂μ.prod ρ :=
      lintegral_mono (fun p => normalizedBallSlice_le hq₁ hq₂ hab hR ha hb hv t p.2 p.1)
    _ = ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) *
        ∫⁻ p, extendedKernel q v p ∂μ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod _ hm.aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) *
        ENNReal.ofReal (expectationConstant q / ‖v‖) := mul_le_mul_right hμ _
    _ = ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖ *
        (expectationConstant q / ‖v‖)) := (ENNReal.ofReal_mul hc).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (averagingCoefficient_bound hq₁ hq₂ hR (sub_pos.mpr hab) (norm_pos_iff.mpr hv))

def geometricConstant (q : ℝ) : ℝ :=
  expectationConstant q * (2 + AxialSlices.lineConstant q * AxialSlices.scalarConstant (1 - q))

theorem geometricConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < geometricConstant q := by
  have he := expectationConstant_pos q
  have hl := AxialSlices.lineConstant_pos hq₁
  have hs := AxialSlices.scalarConstant_pos (show -1 < 1 - q by linarith)
  unfold geometricConstant
  positivity

private theorem geometricConstant_bound {q R ell : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 < R) (hell : 0 < ell) :
    expectationConstant q * (2 * R * ell + intervalCoefficient q R ell) ≤
      geometricConstant q * (R * ell + R ^ (q - 1) * ell ^ (2 - q)) := by
  have hu : 0 ≤ R * ell := by positivity
  have hs : 0 ≤ R ^ (q - 1) * ell ^ (2 - q) := by positivity
  have hk : 0 ≤ AxialSlices.lineConstant q * AxialSlices.scalarConstant (1 - q) :=
    mul_nonneg (AxialSlices.lineConstant_pos hq₁).le
      (AxialSlices.scalarConstant_pos (by linarith)).le
  unfold geometricConstant intervalCoefficient
  rw [mul_assoc (expectationConstant q)]
  apply mul_le_mul_of_nonneg_left _ (expectationConstant_pos q).le
  nlinarith [mul_nonneg hk hu]

theorem gaussian_geometric_interval {q d a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(gaussianLaw d).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  (normalizedBallSlice_product_bound hq₁ hq₂ hab hR ha hb hv t (gaussianLaw d) ρ
    (gaussian_extendedKernel_lintegral_le hq₁ hq₂ hd hv)).trans
      (ENNReal.ofReal_le_ofReal (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hab)))

theorem uniformDisk_geometric_interval {q d a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(uniformDiskLaw d).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  (normalizedBallSlice_product_bound hq₁ hq₂ hab hR ha hb hv t (uniformDiskLaw d) ρ
    (uniformDisk_extendedKernel_lintegral_le hq₁ hq₂ hd hv)).trans
      (ENNReal.ofReal_le_ofReal (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hab)))

theorem atom_geometric_interval {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(Measure.dirac (0 : Transverse)).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  (normalizedBallSlice_product_bound hq₁ hq₂ hab hR ha hb hv t (Measure.dirac 0) ρ
    (atom_extendedKernel_lintegral_le q hv)).trans
      (ENNReal.ofReal_le_ofReal (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hab)))

/-- The component laws permitted in the manuscript's transverse mixtures. -/
def IsDiskOrAtomLaw (μ : Measure Transverse) : Prop :=
  μ = Measure.dirac (0 : Transverse) ∨ ∃ d : ℝ, 0 < d ∧ μ = uniformDiskLaw d

theorem isProbabilityMeasure_of_diskOrAtomLaw {μ : Measure Transverse} (hμ : IsDiskOrAtomLaw μ) :
    IsProbabilityMeasure μ := by
  rcases hμ with rfl | ⟨d, hd, rfl⟩
  · infer_instance
  · exact uniformDiskLaw_isProbabilityMeasure hd

theorem ae_regularTransverse_of_diskOrAtomLaw {v : Transverse} (hv : v ≠ 0)
    {μ : Measure Transverse} (hμ : IsDiskOrAtomLaw μ) :
    ∀ᵐ p ∂μ, RegularTransverse v p := by
  rcases hμ with rfl | ⟨d, _hd, rfl⟩
  · exact ae_regularTransverse_atom hv
  · exact ae_regularTransverse_uniformDisk hv d

theorem extendedKernel_bound_of_diskOrAtomLaw {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {v : Transverse} (hv : v ≠ 0) {μ : Measure Transverse} (hμ : IsDiskOrAtomLaw μ) :
    (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rcases hμ with rfl | ⟨d, hd, rfl⟩
  · exact atom_extendedKernel_lintegral_le q hv
  · exact uniformDisk_extendedKernel_lintegral_le hq₁ hq₂ hd hv

theorem diskAtomMixture_isProbabilityMeasure {ι : Type*} [MeasurableSpace ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (L : ι → Measure Transverse)
    (hL : Measurable L) (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i)) :
    IsProbabilityMeasure (ν.bind L) :=
  isProbabilityMeasure_bind hL.aemeasurable
    (hLaw.mono (fun _ hi => isProbabilityMeasure_of_diskOrAtomLaw hi))

theorem ae_regularTransverse_diskAtomMixture {ι : Type*} [MeasurableSpace ι]
    (ν : Measure ι) (L : ι → Measure Transverse) (hL : Measurable L)
    (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i)) {v : Transverse} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.bind L, RegularTransverse v p := by
  rw [ae_iff]
  change (ν.bind L) ({p | RegularTransverse v p}ᶜ) = 0
  rw [Measure.bind_apply (measurableSet_regularTransverse v).compl hL.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hLaw] with i hi
  exact (ae_iff.mp (ae_regularTransverse_of_diskOrAtomLaw hv hi))

theorem diskAtomMixture_extendedKernel_bound {ι : Type*} [MeasurableSpace ι]
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (ν : Measure ι) [IsProbabilityMeasure ν] (L : ι → Measure Transverse)
    (hL : Measurable L) (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i))
    {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂ν.bind L) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [Measure.lintegral_bind hL.aemeasurable (measurable_extendedKernel q v).aemeasurable]
  calc
    _ ≤ ∫⁻ _ : ι, ENNReal.ofReal (expectationConstant q / ‖v‖) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hLaw] with i hi
      exact extendedKernel_bound_of_diskOrAtomLaw hq₁ hq₂ hv hi
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

/-- The geometric interval estimate for every probability mixture of centered
uniform disks and the atom at zero, with an arbitrary axial probability law. -/
theorem diskAtomMixture_geometric_interval {ι : Type*} [MeasurableSpace ι]
    {q a b R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (ν : Measure ι) [IsProbabilityMeasure ν] (L : ι → Measure Transverse)
    (hL : Measurable L) (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(ν.bind L).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  (normalizedBallSlice_product_bound hq₁ hq₂ hab hR ha hb hv t (ν.bind L) ρ
    (diskAtomMixture_extendedKernel_bound hq₁ hq₂ ν L hL hLaw hv)).trans
      (ENNReal.ofReal_le_ofReal (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hab)))

theorem ballLineRegion_eq_empty_of_outside {R z : ℝ} (hR : 0 ≤ R)
    (hz : z < -R ∨ R < z) (e v : Transverse) (D : ℝ) :
    ballLineRegion e v D z R = ∅ := by
  ext s
  simp only [ballLineRegion, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hs
  rcases hz with hz | hz <;> nlinarith [sq_nonneg ‖TransverseLine.line e D s - v‖]

/-- The genuine ball already clips the axial displacement to `[-R,R]`.
The single lower endpoint is removed only on a Lebesgue-null set. -/
theorem ballLineMass_clip {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (e v : Transverse) (A B a b : ℝ) :
    ballLineMass q e v A B R a b =
      ballLineMass q e v A B R (max (-R) a) (min R b) := by
  let F : ℝ → ℝ≥0∞ := fun z => ∫⁻ s in ballLineRegion e v (A - B * z) z R,
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)
  have hz : ∀ᵐ z ∂(volume.restrict (Ioc a b)), z ≠ -R :=
    ae_restrict_of_ae (volume.ae_ne (-R))
  have hF : ∀ z, z ∉ Ioc (-R) R → z ≠ -R → F z = 0 := by
    intro z hout hne
    have ho : z < -R ∨ R < z := by
      by_cases hleft : -R < z
      · right
        have hn : ¬ z ≤ R := fun h => hout ⟨hleft, h⟩
        exact lt_of_not_ge hn
      · left
        exact lt_of_le_of_ne (le_of_not_gt hleft) hne
    simp only [F, ballLineRegion_eq_empty_of_outside hR ho, Measure.restrict_empty, lintegral_zero_measure]
  have hi : Ioc (-R) R ∩ Ioc a b = Ioc (max (-R) a) (min R b) := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  change (∫⁻ z in Ioc a b, F z) = ∫⁻ z in Ioc (max (-R) a) (min R b), F z
  calc
    _ = ∫⁻ z in Ioc a b, (Ioc (-R) R).indicator F z := by
      apply lintegral_congr_ae
      filter_upwards [hz] with z hne
      by_cases hmem : z ∈ Ioc (-R) R
      · rw [indicator_of_mem hmem]
      · rw [indicator_of_notMem hmem, hF z hmem hne]
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hi]

theorem normalizedBallSlice_clip {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (v : Transverse) (t : ℝ) (p : Transverse) (alpha a b : ℝ) :
    normalizedBallSlice q v t p alpha R a b =
      normalizedBallSlice q v t p alpha R (max (-R) a) (min R b) := by
  classical
  by_cases hp : RegularTransverse v p
  · simp only [normalizedBallSlice, hp, ↓reduceIte]
    rw [ballLineMass_clip hR]
  · simp only [normalizedBallSlice, hp, ↓reduceIte]

/-- The interval estimate for arbitrary axial endpoints, using the actual ball
restriction to clip the interval before applying the scalar estimate. -/
theorem geometric_interval_of_kernel_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (_hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hreg : ∀ᵐ p ∂μ, RegularTransverse v p)
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂μ.prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) := by
  have heq : (fun p : Transverse × ℝ => normalizedBallSlice q v t p.1 p.2 R a b) =
      fun p => normalizedBallSlice q v t p.1 p.2 R (max (-R) a) (min R b) := by
    funext p
    exact normalizedBallSlice_clip hR.le q v t p.1 p.2 a b
  rw [heq]
  by_cases hc : max (-R) a < min R b
  · have hbound := normalizedBallSlice_product_bound hq₁ hq₂ hc hR
      (le_max_left _ _) (min_le_left _ _) hv t μ ρ hμ
    have hgeom := ENNReal.ofReal_le_ofReal
      (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hc))
    apply (hbound.trans hgeom).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (geometricConstant_pos hq₁ hq₂).le
    have hlen : min R b - max (-R) a ≤ b - a := by
      linarith [min_le_right R b, le_max_right (-R) a]
    have hp := Real.rpow_le_rpow (sub_pos.mpr hc).le hlen (show 0 ≤ 2 - q by linarith)
    exact add_le_add (mul_le_mul_of_nonneg_left hlen hR.le)
      (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hR.le _))
  · have hempty : Ioc (max (-R) a) (min R b) = ∅ := Ioc_eq_empty hc
    have hi : (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R
        (max (-R) a) (min R b) ∂μ.prod ρ) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_regularTransverse_prod hreg] with p hp
      simp only [normalizedBallSlice, hp, ↓reduceIte, ballLineMass, hempty,
        Measure.restrict_empty, lintegral_zero_measure, mul_zero, Pi.zero_apply]
    rw [hi]
    exact bot_le

theorem gaussian_geometric_interval_any {q d a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) (hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(gaussianLaw d).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  geometric_interval_of_kernel_bound hq₁ hq₂ hab hR hv t (gaussianLaw d) ρ
    (ae_regularTransverse_gaussian hv d) (gaussian_extendedKernel_lintegral_le hq₁ hq₂ hd hv)

theorem diskAtomMixture_geometric_interval_any {ι : Type*} [MeasurableSpace ι]
    {q a b R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (ν : Measure ι) [IsProbabilityMeasure ν] (L : ι → Measure Transverse)
    (hL : Measurable L) (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂(ν.bind L).prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) :=
  geometric_interval_of_kernel_bound hq₁ hq₂ hab hR hv t (ν.bind L) ρ
    (ae_regularTransverse_diskAtomMixture ν L hL hLaw hv)
    (diskAtomMixture_extendedKernel_bound hq₁ hq₂ ν L hL hLaw hv)

def geometricTotalConstant (q : ℝ) : ℝ := (2 + (2 : ℝ) ^ (2 - q)) * geometricConstant q

/-- Taking the full axial range gives the uniform `C_q R²` ball estimate. -/
theorem geometric_total_of_kernel_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 1 ≤ R) {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hreg : ∀ᵐ p ∂μ, RegularTransverse v p)
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R ∂μ.prod ρ) ≤
      ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have hR₀ : 0 < R := by linarith
  have h := geometric_interval_of_kernel_bound hq₁ hq₂ (by linarith : -R < R) hR₀ hv t μ ρ hreg hμ
  have hpow : R ^ (q - 1) * (2 * R) ^ (2 - q) = (2 : ℝ) ^ (2 - q) * R := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR₀.le]
    calc
      _ = (2 : ℝ) ^ (2 - q) * (R ^ (q - 1) * R ^ (2 - q)) := by ring
      _ = _ := by rw [← Real.rpow_add hR₀, show q - 1 + (2 - q) = 1 by ring, Real.rpow_one]
  rw [show R - -R = 2 * R by ring, hpow] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hR₂ : R ≤ R ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hR₂ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - q))
  unfold geometricTotalConstant
  nlinarith [mul_nonneg (geometricConstant_pos hq₁ hq₂).le
    (sub_nonneg.mpr hp)]

theorem gaussian_geometric_total {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 < d) (hR : 1 ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R ∂(gaussianLaw d).prod ρ) ≤
      ENNReal.ofReal (geometricTotalConstant q * R ^ 2) :=
  geometric_total_of_kernel_bound hq₁ hq₂ hR hv t (gaussianLaw d) ρ
    (ae_regularTransverse_gaussian hv d) (gaussian_extendedKernel_lintegral_le hq₁ hq₂ hd hv)

theorem diskAtomMixture_geometric_total {ι : Type*} [MeasurableSpace ι]
    {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 1 ≤ R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (ν : Measure ι) [IsProbabilityMeasure ν] (L : ι → Measure Transverse)
    (hL : Measurable L) (hLaw : ∀ᵐ i ∂ν, IsDiskOrAtomLaw (L i))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R ∂(ν.bind L).prod ρ) ≤
      ENNReal.ofReal (geometricTotalConstant q * R ^ 2) :=
  geometric_total_of_kernel_bound hq₁ hq₂ hR hv t (ν.bind L) ρ
    (ae_regularTransverse_diskAtomMixture ν L hL hLaw hv)
    (diskAtomMixture_extendedKernel_bound hq₁ hq₂ ν L hL hLaw hv)

end BoltzmannNonuniqueness.GeometricSlice

end

end OAI
