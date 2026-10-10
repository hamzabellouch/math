import OAI.Analysis.Mahler.RadialPrimitiveDeriv
import OAI.Analysis.Mahler.VerticalRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- The actual inverse radius in a vertical line of Omega. -/
noncomputable def verticalRadius (q t : ℝ) : ℝ :=
  ‖MahlerConformal.inverseF ((q : ℂ)+(t : ℂ)*Complex.I)‖

lemma sqrt_verticalRadiusSq (q t : ℝ) :
    sqrt (MahlerConformal.verticalRadiusSq q t) = verticalRadius q t := by
  unfold MahlerConformal.verticalRadiusSq verticalRadius
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem verticalRadius_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    verticalRadius (MahlerConformal.Q r θ) (MahlerConformal.S r θ) = r := by
  rw [← sqrt_verticalRadiusSq, MahlerConformal.verticalRadiusSq_polar hr hr1,
    Real.sqrt_sq hr.le]

theorem hasDerivAt_verticalRadius_polar {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (verticalRadius (MahlerConformal.Q r θ))
      (MahlerConformal.B r θ/(r*‖deriv MahlerConformal.F (MahlerConformal.polar r θ)‖^2))
      (MahlerConformal.S r θ) := by
  have hv := MahlerConformal.verticalRadiusSq_polar hr hr1 θ
  have hnonzero : MahlerConformal.verticalRadiusSq (MahlerConformal.Q r θ)
      (MahlerConformal.S r θ) ≠ 0 := by rw [hv]; positivity
  have h := (MahlerConformal.hasDerivAt_verticalRadiusSq_polar hr hr1).sqrt hnonzero
  simp only [sqrt_verticalRadiusSq, verticalRadius_polar hr hr1] at h
  convert h using 1
  field_simp

theorem verticalRadius_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    verticalRadius q (fiberHeight q r) = r := by
  have hs := fiberAngle_spec hr
  have h := verticalRadius_polar hr.1 hr.2.1 (fiberAngle q r)
  rw [hs.2] at h
  exact h

theorem hasDerivAt_verticalRadius_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    HasDerivAt (verticalRadius q) (deriv (fiberHeight q) r)⁻¹ (fiberHeight q r) := by
  have hs := fiberAngle_spec hr
  have h := hasDerivAt_verticalRadius_polar hr.1 hr.2.1 (θ := fiberAngle q r)
  rw [hs.2] at h
  rw [(hasDerivAt_fiberHeight hr).deriv, inv_div]
  exact h

/-- Composition with the actual inverse radius has the prescribed vertical
primitive derivative, before taking the endpoint limit and global integral. -/
theorem hasDerivAt_actual_vertical_primitive {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ m (verticalRadius q t))
      ((4*m/Real.pi)*r^(2*m-2 : ℝ) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2)
      (fiberHeight q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hρ := hasDerivAt_verticalRadius_fiber hmem
  have hP := hasDerivAt_radialPrimitive hm hr₀ hq hr
  have h := hP.comp_of_eq (fiberHeight q r) hρ (verticalRadius_fiber hmem).symm
  have hquot := radial_density_div_vertical_speed (m := m) hmem
  simpa only [Function.comp_def, ← div_eq_mul_inv, hquot] using h

lemma fiber_image_eq {q r : ℝ} (hr : r ∈ fiberDomain q) :
    (q : ℂ)+(fiberHeight q r : ℂ)*Complex.I =
      MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)) := by
  have h := MahlerConformal.Q_add_S_I r (fiberAngle q r)
  rw [(fiberAngle_spec hr).2] at h
  exact h

lemma fiber_image_mem {q r : ℝ} (hr : r ∈ fiberDomain q) :
    (q : ℂ)+(fiberHeight q r : ℂ)*Complex.I ∈ MahlerConformal.Omega := by
  rw [fiber_image_eq hr]
  refine ⟨MahlerConformal.polar r (fiberAngle q r), ?_, rfl⟩
  simpa [MahlerConformal.norm_polar hr.1.le] using hr.2.1

lemma inverseF_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I) =
      MahlerConformal.polar r (fiberAngle q r) := by
  rw [fiber_image_eq hr]
  apply MahlerConformal.inverseF_left
  simpa [MahlerConformal.norm_polar hr.1.le] using hr.2.1

/-- The derivative along the upper fiber, with h and h'
being the constructed holomorphic inverse and its derivative. -/
theorem actual_vertical_primitive_derivative {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ m (verticalRadius q t))
      ((4*m/Real.pi)*
        ‖MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)‖^(2*m-2 : ℝ)*
        ‖deriv MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)‖^2)
      (fiberHeight q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have h := hasDerivAt_actual_vertical_primitive hm hr₀ hq hr
  rw [(MahlerConformal.hasDerivAt_inverseF (fiber_image_mem hmem)).deriv,
    inverseF_fiber hmem, MahlerConformal.norm_polar hmem.1.le, norm_inv, inv_pow]
  simpa only [div_eq_mul_inv] using h

/-- The actual inverse-coordinate primitive has the concrete planar error bound. -/
theorem actual_vertical_primitive_bound {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    radialPrimitive q r₀ m (verticalRadius q (fiberHeight q r)) ≤
      ‖MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)‖^(2*m : ℝ)+planarError m := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  rw [verticalRadius_fiber hmem, inverseF_fiber hmem, MahlerConformal.norm_polar hmem.1.le]
  exact fiber_primitive_bound hm hr₀ hq ⟨hr.1.le,hr.2⟩

end SymmetricMahler

end OAI
