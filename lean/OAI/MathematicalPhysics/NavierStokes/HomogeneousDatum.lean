import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The prescribed homogeneous axisymmetric datum

The field `StationaryNS.homogeneousDatum` is the datum
`V(130z / (r² + z²))` from the homogeneous-datum subsection of
*Stationary instability and nonuniqueness for axisymmetric swirl-free Navier–Stokes*.
It is homogeneous of degree `-1`, axisymmetric and swirl-free, smooth and classically
solenoidal away from the origin, and square integrable on every compact set.
-/

noncomputable section

namespace StationaryNS

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Field := Space → Space

/-- The square of the distance to the origin, in Cartesian coordinates. -/
def radiusSq (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

/-- The homogeneous datum `V(130z/(r²+z²))` of `sa:homogeneous-datum`,
written in Cartesian coordinates. Its value at the origin is fixed to zero;
that value has no bearing on its distributional interpretation. -/
def homogeneousDatum (x : Space) : Space :=
  WithLp.toLp 2 ![
    130 * x 0 * (x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2) / radiusSq x ^ 2,
    130 * x 1 * (x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2) / radiusSq x ^ 2,
    -260 * x 2 ^ 3 / radiusSq x ^ 2]

theorem radiusSq_ne_zero {x : Space} (hx : x ≠ 0) : radiusSq x ≠ 0 := by
  intro hzero
  have hzero' : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 0 := hzero
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hx2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  apply hx
  ext i
  fin_cases i <;> simp [hx0, hx1, hx2]

theorem radiusSq_smul (t : ℝ) (x : Space) : radiusSq (t • x) = t ^ 2 * radiusSq x := by
  simp only [radiusSq, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] theorem homogeneousDatum_zero : homogeneousDatum 0 = 0 := by
  ext i
  fin_cases i <;> simp [homogeneousDatum, radiusSq]

/-- Homogeneity of degree `-1`, with every nonzero real scale allowed. -/
theorem homogeneousDatum_smul {t : ℝ} (ht : t ≠ 0) (x : Space) :
    homogeneousDatum (t • x) = t⁻¹ • homogeneousDatum x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hq := radiusSq_ne_zero hx
  ext i
  fin_cases i <;>
    simp [homogeneousDatum, radiusSq_smul, PiLp.smul_apply] <;>
    field_simp

/-- Reflection in the horizontal plane. -/
def reflectZ (x : Space) : Space := WithLp.toLp 2 ![x 0, x 1, -x 2]

@[simp] theorem radiusSq_reflectZ (x : Space) : radiusSq (reflectZ x) = radiusSq x := by
  simp [radiusSq, reflectZ]

/-- Positive vector reflection parity of the prescribed homogeneous datum. -/
theorem homogeneousDatum_parity (x : Space) :
    homogeneousDatum (reflectZ x) = reflectZ (homogeneousDatum x) := by
  ext i
  fin_cases i <;> simp [homogeneousDatum, reflectZ, radiusSq]
  ring

/-- The Cartesian angular component is zero. -/
theorem homogeneousDatum_swirlFree (x : Space) :
    x 0 * homogeneousDatum x 1 - x 1 * homogeneousDatum x 0 = 0 := by
  simp [homogeneousDatum]
  ring

/-- The datum is smooth away from its singular point. -/
theorem homogeneousDatum_contDiffOn :
    ContDiffOn ℝ ⊤ homogeneousDatum ({0}ᶜ : Set Space) := by
  have hp (i : Fin 3) : ContDiff ℝ ⊤ (fun x : Space => x i) := contDiff_piLp_apply 2
  have hq : ContDiff ℝ ⊤ radiusSq := by
    exact ((hp 0).pow 2 |>.add ((hp 1).pow 2)).add ((hp 2).pow 2)
  have hden (x : Space) (hx : x ∈ ({0}ᶜ : Set Space)) : radiusSq x ^ 2 ≠ 0 := by
    apply pow_ne_zero
    apply radiusSq_ne_zero
    simpa using hx
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i <;> simp only [homogeneousDatum, PiLp.toLp_apply] <;>
    apply ContDiffOn.div _ ((hq.pow 2).contDiffOn) hden <;> fun_prop

/-- The classical radial drift `x·∇u`. -/
def drift (u : Field) (x : Space) : Space := fderiv ℝ u x x

/-- Euler's identity for the prescribed degree `-1` datum. -/
theorem homogeneousDatum_euler {x : Space} (hx : x ≠ 0) :
    drift homogeneousDatum x + homogeneousDatum x = 0 := by
  have hnhds : ({0}ᶜ : Set Space) ∈ nhds x :=
    isOpen_compl_singleton.mem_nhds (by simpa using hx)
  have hu : DifferentiableAt ℝ homogeneousDatum x :=
    (homogeneousDatum_contDiffOn.contDiffAt hnhds).differentiableAt (by simp)
  have hlin : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hu' : HasFDerivAt homogeneousDatum (fderiv ℝ homogeneousDatum x)
      ((fun t : ℝ => t • x) 1) := by
    simpa using hu.hasFDerivAt
  have hcomp₀ := HasFDerivAt.comp_hasDerivAt 1 hu' hlin
  have hcomp : HasDerivAt (fun t : ℝ => homogeneousDatum (t • x))
      (drift homogeneousDatum x) 1 := by
    simpa only [drift, Function.comp_def] using hcomp₀
  have heq : (fun t : ℝ => homogeneousDatum (t • x)) =ᶠ[nhds 1]
      (fun t => t⁻¹ • homogeneousDatum x) := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0)] with t ht
    exact homogeneousDatum_smul ht x
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹ • homogeneousDatum x)
      (-homogeneousDatum x) 1 := by
    simpa using (hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0)).smul_const
      (homogeneousDatum x)
  rw [hcomp.unique (hinv.congr_of_eventuallyEq heq), neg_add_cancel]

/-- Cartesian divergence at points where the field is differentiable. -/
def divergence (u : Field) (x : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => u y i) x (EuclideanSpace.single i 1)

/-- The datum is classically solenoidal off the origin. Distributional
solenoidality across the singular point needs a separate small-sphere estimate. -/
theorem homogeneousDatum_divergence {x : Space} (hx : x ≠ 0) :
    divergence homogeneousDatum x = 0 := by
  have hp (i : Fin 3) : HasFDerivAt (fun y : Space => y i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hq := ((hp 0).pow 2 |>.add ((hp 1).pow 2)).add ((hp 2).pow 2)
  have hq' : HasFDerivAt radiusSq _ x := hq
  have hd := (hasDerivAt_inv (pow_ne_zero 2 (radiusSq_ne_zero hx))).comp_hasFDerivAt x
    (hq'.pow 2)
  have hxy := ((hp 0).pow 2 |>.add ((hp 1).pow 2)).sub ((hp 2).pow 2)
  have h0 := (((hp 0).const_mul 130).fun_mul hxy).fun_mul hd
  have h1 := (((hp 1).const_mul 130).fun_mul hxy).fun_mul hd
  have h2 := (((hp 2).pow 3).const_mul (-260)).fun_mul hd
  simp only [divergence, Fin.sum_univ_three, homogeneousDatum, PiLp.toLp_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, div_eq_mul_inv]
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply] at h0 h1 h2
  rw [h0.fderiv, h1.fderiv, h2.fderiv]
  simp [PiLp.proj_apply]
  field_simp [radiusSq_ne_zero hx]
  unfold radiusSq
  ring

/-- Unit vector along the axis of symmetry. -/
def axialUnit : Space := EuclideanSpace.single 2 1

/-- Invariance under the full orthogonal group fixing the vertical axis
pointwise. Unlike invariance under rotations alone, this includes reflections
in vertical planes and excludes a swirl component. -/
def AxisymmetricSwirlFree (u : Field) : Prop :=
  ∀ R : Space ≃ₗᵢ[ℝ] Space, R axialUnit = axialUnit → ∀ x, u (R x) = R (u x)

theorem radiusSq_eq_normSq (x : Space) : radiusSq x = ‖x‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, radiusSq, Real.norm_eq_abs]

/-- A coordinate-free expression useful for the orthogonal symmetries. -/
theorem homogeneousDatum_vector (x : Space) :
    homogeneousDatum x = (130 / radiusSq x ^ 2) •
      ((radiusSq x - 2 * x 2 ^ 2) • x - (radiusSq x * x 2) • axialUnit) := by
  ext i
  fin_cases i <;> simp [homogeneousDatum, axialUnit, radiusSq] <;> ring

theorem homogeneousDatum_axisymmetricSwirlFree : AxisymmetricSwirlFree homogeneousDatum := by
  intro R hR x
  have hq : radiusSq (R x) = radiusSq x := by
    simp only [radiusSq_eq_normSq, R.norm_map]
  have hz : R x 2 = x 2 := by
    have hi := R.inner_map_map axialUnit x
    rw [hR] at hi
    simpa [axialUnit, EuclideanSpace.inner_single_left] using hi
  rw [homogeneousDatum_vector, homogeneousDatum_vector, hq, hz]
  simp only [map_smul, map_sub, hR]

/-- The singular datum obeys the pointwise inverse-distance bound, interpreted
with Lean's zero inverse at the origin. -/
theorem homogeneousDatum_norm (x : Space) : ‖homogeneousDatum x‖ ≤ 260 / ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq : 0 < radiusSq x := by rw [radiusSq_eq_normSq]; positivity
  have hz : |x 2| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 2
  have hzq : x 2 ^ 2 ≤ radiusSq x := by
    unfold radiusSq
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have ha : |radiusSq x - 2 * x 2 ^ 2| ≤ radiusSq x :=
    abs_le.mpr ⟨by linarith, by nlinarith [sq_nonneg (x 2)]⟩
  have he : ‖axialUnit‖ = 1 := by simp [axialUnit]
  calc
    ‖homogeneousDatum x‖ = (130 / radiusSq x ^ 2) *
        ‖(radiusSq x - 2 * x 2 ^ 2) • x - (radiusSq x * x 2) • axialUnit‖ := by
      rw [homogeneousDatum_vector, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ (130 / radiusSq x ^ 2) *
        (‖(radiusSq x - 2 * x 2 ^ 2) • x‖ + ‖(radiusSq x * x 2) • axialUnit‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = (130 / radiusSq x ^ 2) *
        (|radiusSq x - 2 * x 2 ^ 2| * ‖x‖ + radiusSq x * |x 2|) := by
      rw [norm_smul, norm_smul, he]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hq, mul_one]
    _ ≤ (130 / radiusSq x ^ 2) * (radiusSq x * ‖x‖ + radiusSq x * ‖x‖) := by
      gcongr
    _ = 260 / ‖x‖ := by
      rw [radiusSq_eq_normSq]
      field_simp
      ring

theorem homogeneousDatum_measurable : Measurable homogeneousDatum := by
  have hp (i : Fin 3) : Measurable (fun x : Space => x i) :=
    (contDiff_piLp_apply 2 (𝕜 := ℝ) (n := 0)).continuous.measurable
  have hq : Measurable radiusSq := by
    exact ((hp 0).pow_const 2 |>.add ((hp 1).pow_const 2)).add ((hp 2).pow_const 2)
  have heq : homogeneousDatum = fun x : Space => (130 / radiusSq x ^ 2) •
      ((radiusSq x - 2 * x 2 ^ 2) • x - (radiusSq x * x 2) • axialUnit) :=
    funext homogeneousDatum_vector
  rw [heq]
  fun_prop

open MeasureTheory in
/-- Local square integrability, including the singular point. -/
theorem homogeneousDatum_sq_locallyIntegrable :
    LocallyIntegrable (fun x : Space => ‖homogeneousDatum x‖ ^ 2) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  apply locallyIntegrable_of_norm_le_rpow (by rw [hdim]; norm_num)
    (C := 260 ^ 2) (α := 2) (by rw [hdim]; norm_num)
  · apply Filter.Eventually.of_forall
    intro x
    calc
      ‖‖homogeneousDatum x‖ ^ 2‖ = ‖homogeneousDatum x‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ (260 / ‖x‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (homogeneousDatum_norm x) 2
      _ = 260 ^ 2 * ‖x‖ ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]
        ring
  · exact (homogeneousDatum_measurable.norm.pow_const 2).aestronglyMeasurable

open MeasureTheory in
/-- The datum belongs to `L²` on every compact subset of three-dimensional space. -/
theorem homogeneousDatum_memLp_two_on_compact {K : Set Space} (hK : IsCompact K) :
    MemLp homogeneousDatum 2 (volume.restrict K) := by
  rw [memLp_two_iff_integrable_sq_norm homogeneousDatum_measurable.aestronglyMeasurable]
  exact homogeneousDatum_sq_locallyIntegrable.integrableOn_isCompact hK

end StationaryNS

end

end OAI
