import OAI.Geometry.PolarProducts.PotentialDeformation

namespace OAI

universe u36 u37

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothPositivePart

noncomputable section

def primitive (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.smoothTransition s

theorem hasDerivAt_primitive (t : ℝ) : HasDerivAt primitive (Real.smoothTransition t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact Real.smoothTransition.continuous.intervalIntegrable _ _
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun _ _ => Real.smoothTransition.continuousAt) t (mem_univ t)
  · exact Real.smoothTransition.continuousAt

@[simp] theorem deriv_primitive : deriv primitive = Real.smoothTransition :=
  funext (fun t => (hasDerivAt_primitive t).deriv)

theorem primitive_smooth : ContDiff ℝ ∞ primitive := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_primitive t).differentiableAt,
    deriv_primitive ▸ Real.smoothTransition.contDiff⟩

theorem primitive_of_nonpos {t : ℝ} (ht : t ≤ 0) : primitive t = 0 := by
  calc
    primitive t = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply Real.smoothTransition.zero_of_nonpos
      exact le_trans hs.2 (max_eq_left ht).le
    _ = 0 := intervalIntegral.integral_zero

theorem primitive_one_mem : primitive 1 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro s _
    exact Real.smoothTransition.nonneg s
  · calc
      primitive 1 ≤ ∫ s in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact Real.smoothTransition.continuous.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro s _
          exact Real.smoothTransition.le_one s
      _ = 1 := by simp

theorem primitive_of_one_le {t : ℝ} (ht : 1 ≤ t) : primitive t = t + (primitive 1 - 1) := by
  have he : (∫ s in (1 : ℝ)..t, Real.smoothTransition s) = t - 1 := by
    calc
      _ = ∫ s in (1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact Real.smoothTransition.one_of_one_le (le_trans (by simp [ht]) hs.1)
      _ = t - 1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (Real.smoothTransition.continuous.intervalIntegrable (μ := volume) (0 : ℝ) 1)
    (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) t)
  change primitive 1 + _ = primitive t at hadd
  rw [he] at hadd
  linarith

def shift : ℝ := primitive 1 - 1

theorem shift_mem : shift ∈ Icc (-1 : ℝ) 0 := by
  have h := primitive_one_mem
  change -1 ≤ primitive 1 - 1 ∧ primitive 1 - 1 ≤ 0
  constructor <;> linarith [h.1, h.2]

def positivePart (t : ℝ) : ℝ := primitive (t - shift)

theorem positivePart_smooth : ContDiff ℝ ∞ positivePart :=
  primitive_smooth.comp (contDiff_id.sub contDiff_const)

theorem positivePart_zero {t : ℝ} (ht : t ≤ -1) : positivePart t = 0 := by
  apply primitive_of_nonpos
  linarith [shift_mem.1]

theorem positivePart_eq_self {t : ℝ} (ht : 1 ≤ t) : positivePart t = t := by
  rw [positivePart, primitive_of_one_le (by linarith [shift_mem.2])]
  unfold shift
  ring

theorem deriv_positivePart (t : ℝ) : deriv positivePart t = Real.smoothTransition (t - shift) := by
  change deriv (fun t => primitive (t - shift)) t = _
  simpa only [mul_one, Function.comp_def, id_eq] using
    ((hasDerivAt_primitive (t - shift)).comp t ((hasDerivAt_id t).sub_const shift)).deriv

theorem deriv_positivePart_mem (t : ℝ) : deriv positivePart t ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_positivePart]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem second_deriv_positivePart_nonneg (t : ℝ) : 0 ≤ deriv (deriv positivePart) t := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  rw [deriv_positivePart, deriv_positivePart]
  exact Real.smoothTransition.monotone (sub_le_sub_right hxy _)

def smoothMax (h p : ℝ) : ℝ := p + positivePart (h - p)

theorem smoothMax_left {h p : ℝ} (hp : p + 1 ≤ h) : smoothMax h p = h := by
  rw [smoothMax, positivePart_eq_self (by linarith)]
  ring

theorem smoothMax_right {h p : ℝ} (hp : h + 1 ≤ p) : smoothMax h p = p := by
  rw [smoothMax, positivePart_zero (by linarith), add_zero]

end
end SmoothPositivePart

namespace ComplexPotential

open TensorCalculus SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u36} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance maxOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance maxOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance maxTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance maxTwoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem IsPSHAt.smoothMax {J : E →L[ℝ] E} (hJ : ∀ a, J (J a) = -a)
    {φ ψ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => smoothMax (φ y) (ψ y)) x := by
  have hdiff := hφ.1.sub hψ.1
  have hs : ContDiffAt ℝ ∞ (positivePart ∘ fun y => φ y - ψ y) x :=
    positivePart_smooth.contDiffAt.comp x hdiff
  refine ⟨hψ.1.add hs, fun a => ?_⟩
  change 0 ≤ ddc J (fun y => ψ y + (positivePart ∘ fun z => φ z - ψ z) y) x a (J a)
  rw [ddc_add J hψ.1 hs, add_apply, add_apply,
    ddc_scalar_comp_complex_line J hJ hdiff positivePart_smooth.contDiffAt,
    ddc_sub J hφ.1 hψ.1, sub_apply, sub_apply]
  have hβ := deriv_positivePart_mem (φ x - ψ x)
  have h2 := second_deriv_positivePart_nonneg (φ x - ψ x)
  have hpos : 0 ≤ (1 - deriv positivePart (φ x - ψ x)) * ddc J ψ x a (J a) +
      deriv positivePart (φ x - ψ x) * ddc J φ x a (J a) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hβ.2) (hψ.2 a))
      (mul_nonneg hβ.1 (hφ.2 a))
  have hquad : 0 ≤ deriv (deriv positivePart) (φ x - ψ x) *
      ((fderiv ℝ (fun y => φ y - ψ y) x a)^2 +
        (fderiv ℝ (fun y => φ y - ψ y) x (J a))^2) / 4 := by positivity
  nlinarith

theorem IsPSHAt.congr {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (he : ψ =ᶠ[𝓝 x] φ) : IsPSHAt J ψ x := by
  refine ⟨hφ.1.congr_of_eventuallyEq he, fun a => ?_⟩
  rw [ddc_congr J he]
  exact hφ.2 a

end
end ComplexPotential

namespace ComplexPotential

open SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u37} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

omit [NormedSpace ℝ E] in

def gluedPotential (R : ℝ) (H P : E → ℝ) (x : E) : ℝ := by
  classical
  exact if ‖x‖ < R then if x = 0 then P x else smoothMax (H x) (P x) else H x

omit [NormedSpace ℝ E] in
theorem gluedPotential_outer (R : ℝ) (H P : E → ℝ) {x : E} (hx : R ≤ ‖x‖) :
    gluedPotential R H P x = H x := by
  classical
  simp [gluedPotential, not_lt.mpr hx]

omit [NormedSpace ℝ E] in
theorem gluedPotential_inner {r R : ℝ} (hrR : r < R) (H P : E → ℝ)
    (hdom : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x) {x : E} (hx : ‖x‖ ≤ r) :
    gluedPotential R H P x = P x := by
  classical
  have hR : ‖x‖ < R := hx.trans_lt hrR
  by_cases hzero : x = 0
  · rw [gluedPotential, ite_eq_left hR, ite_eq_left hzero]
  · rw [gluedPotential, ite_eq_left hR, ite_eq_right hzero, smoothMax_right (hdom x hzero hx)]

theorem isPSHAt_gluedPotential (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {U : Set E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (H P : E → ℝ)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hP : ∀ x ∈ U, IsPSHAt J P x)
    (hinner : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x)
    (houter : ∀ x ∈ U, ‖x‖ = R → P x + 1 < H x)
    {x : E} (hx : x ∈ U) : IsPSHAt J (gluedPotential R H P) x := by
  classical
  have hRpos : 0 < R := hr.trans hrR
  by_cases hzero : x = 0
  · have hn : ‖x‖ < r := by simpa [hzero] using hr
    apply (hP x hx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn] with y hy
    exact gluedPotential_inner hrR H P hinner hy.le
  have hHx := hH x hx hzero
  have hPx := hP x hx
  rcases lt_trichotomy ‖x‖ R with hn | hn | hn
  · apply (hHx.smoothMax hJ hPx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn,
      eventually_ne_nhds hzero] with y hy hy0
    simp [gluedPotential, hy, hy0]
  · apply hHx.congr
    have hlt := houter x hx hn
    filter_upwards [(hPx.1.continuousAt.add continuousAt_const).eventually_lt
      hHx.1.continuousAt hlt, eventually_ne_nhds hzero] with y hy hy0
    by_cases hny : ‖y‖ < R
    · simp [gluedPotential, hny, hy0, smoothMax_left hy.le]
    · simp [gluedPotential, hny]
  · apply hHx.congr
    filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hn] with y hy
    exact gluedPotential_outer R H P hy.le

end
end ComplexPotential

end LowerBoundInline

end OAI
