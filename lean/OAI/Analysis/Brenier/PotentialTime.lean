import OAI.Analysis.Brenier.MaxCalculus

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem358.PotentialTimeIntegral

/-- Cauchy--Schwarz against the constant function, without real powers. -/
theorem sq_integral_le_mass_mul_integral_sq
    {T : Type*} [MeasurableSpace T] {ν : Measure T} [IsFiniteMeasure ν]
    {f : T → ℝ} (hmass : 0 < ν.real univ) (hf : Integrable f ν)
    (hf2 : Integrable (fun t => f t ^ 2) ν) :
    (∫ t, f t ∂ν) ^ 2 ≤ ν.real univ * ∫ t, f t ^ 2 ∂ν := by
  let m := ν.real univ
  let z := ∫ t, f t ∂ν
  have hnonneg : 0 ≤ ∫ t, (m * f t - z) ^ 2 ∂ν :=
    integral_nonneg (fun t => sq_nonneg _)
  have heq : (∫ t, (m * f t - z) ^ 2 ∂ν) =
      m ^ 2 * (∫ t, f t ^ 2 ∂ν) - (2 * m * z) * z + m * z ^ 2 := by
    calc
      _ = ∫ t, m ^ 2 * f t ^ 2 - (2 * m * z) * f t + z ^ 2 ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by ring)
      _ = _ := by
        rw [integral_add (f := fun t => m ^ 2 * f t ^ 2 - (2 * m * z) * f t)
          (g := fun _ => z ^ 2) ((hf2.const_mul _).sub (hf.const_mul _)) (integrable_const _),
          integral_sub (f := fun t => m ^ 2 * f t ^ 2)
          (g := fun t => (2 * m * z) * f t) (hf2.const_mul _) (hf.const_mul _), integral_const_mul,
          integral_const_mul, integral_const]
        rfl
  rw [heq] at hnonneg
  have hm : 0 < m := hmass
  change z ^ 2 ≤ m * ∫ t, f t ^ 2 ∂ν
  nlinarith

/-- Spatial squared `L²` control for a pointwise time-integral representation. -/
theorem integral_sq_of_time_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [SFinite μ]
    {v : T → X → ℝ} {F : X → ℝ}
    (hmass : 0 < ν.real univ)
    (hv : Integrable (Function.uncurry v) (ν.prod μ))
    (hv2 : Integrable (fun p : T × X => v p.1 p.2 ^ 2) (ν.prod μ))
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hF : ∀ᵐ x ∂μ, F x = ∫ t, v t x ∂ν) :
    (∫ x, F x ^ 2 ∂μ) ≤
      ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν := by
  calc
    (∫ x, F x ^ 2 ∂μ) ≤
        ∫ x, ν.real univ * (∫ t, v t x ^ 2 ∂ν) ∂μ := by
      apply integral_mono_ae hF2 (hv2.integral_prod_right.const_mul _)
      filter_upwards [hF, hv.prod_left_ae, hv2.prod_left_ae] with x hx hvx hv2x
      rw [hx]
      exact sq_integral_le_mass_mul_integral_sq hmass hvx hv2x
    _ = ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hv2]

/-- A uniform spatial `L²` speed bound integrates to a spatial `L²` displacement bound. -/
theorem sqrt_integral_sq_of_time_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [SFinite μ]
    {v : T → X → ℝ} {F : X → ℝ} {B : ℝ}
    (hmass : 0 < ν.real univ) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) (ν.prod μ))
    (hv2 : Integrable (fun p : T × X => v p.1 p.2 ^ 2) (ν.prod μ))
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hF : ∀ᵐ x ∂μ, F x = ∫ t, v t x ∂ν)
    (hspeed : ∀ᵐ t ∂ν, (∫ x, v t x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ ν.real univ * B := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hmass.le hB, ?_⟩
  calc
    (∫ x, F x ^ 2 ∂μ) ≤ ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν :=
      integral_sq_of_time_integral_le hmass hv hv2 hF2 hF
    _ ≤ ν.real univ * ∫ _ : T, B ^ 2 ∂ν :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hv2.integral_prod_left (integrable_const _) hspeed) hmass.le
    _ = (ν.real univ * B) ^ 2 := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring

/-- The time-interval form of the potential-path estimate, with an a.e. FTC identity. -/
theorem potential_path_L2_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hFTC : ∀ᵐ x ∂μ, u t x - u s x = ∫ r in s..t, v r x)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  have hmass : (volume.restrict (Ioc s t)).real univ = t - s := by
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hst.le)]
  have hFTC' : ∀ᵐ x ∂μ, u t x - u s x = ∫ r, v r x ∂volume.restrict (Ioc s t) := by
    simpa only [intervalIntegral.integral_of_le hst.le] using hFTC
  have h := sqrt_integral_sq_of_time_integral_le
    (by rw [hmass]; exact sub_pos.mpr hst) hB hv hv2 hu2 hFTC' hspeed
  simpa only [hmass, mul_comm] using h

/-- The path estimate with FTC supplied by absolute continuity and an a.e. derivative.
The derivative hypothesis is joint in time and space, as in the finite-max construction. -/
theorem potential_path_L2_bound_of_absolutelyContinuous
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hu : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun r => u r x) s t)
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc s t)).prod μ,
      HasDerivAt (fun r => u r p.2) (v p.1 p.2) p.1)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  apply potential_path_L2_bound hst hB hv hv2 hu2 ?_ hspeed
  have hswap : ∀ᵐ p ∂μ.prod (volume.restrict (Ioc s t)),
      HasDerivAt (fun r => u r p.1) (v p.2 p.1) p.2 :=
    (Measure.measurePreserving_swap (μ := μ)
      (ν := volume.restrict (Ioc s t))).quasiMeasurePreserving.ae hderiv
  filter_upwards [hu, Measure.ae_ae_of_ae_prod hswap] with x hx hdx
  calc
    u t x - u s x = ∫ r in s..t, deriv (fun r => u r x) r :=
      hx.integral_deriv_eq_sub.symm
    _ = ∫ r in s..t, v r x := by
      rw [intervalIntegral.integral_of_le hst.le, intervalIntegral.integral_of_le hst.le]
      apply integral_congr_ae
      exact hdx.mono (fun r hr => hr.deriv)

/-- A locally uniform Lipschitz bound in time is enough for the preceding theorem. -/
theorem potential_path_L2_bound_of_lipschitz
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hu : ∀ᵐ x ∂μ, ∃ L : ℝ≥0, LipschitzOnWith L (fun r => u r x) (Icc s t))
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc s t)).prod μ,
      HasDerivAt (fun r => u r p.2) (v p.1 p.2) p.1)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  apply potential_path_L2_bound_of_absolutelyContinuous hst hB hv hv2 hu2 ?_ hderiv hspeed
  filter_upwards [hu] with x hx
  obtain ⟨L, hL⟩ := hx
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
  simpa only [uIcc_of_le hst.le] using hL

end Problem358.PotentialTimeIntegral

end

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Problem358.PotentialSpeed

/-- Integration over a finite measurable selector is the weighted sum over its fibers. -/
theorem integral_selector {X I : Type*} [MeasurableSpace X]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} [IsFiniteMeasure μ] {sel : X → I} (hsel : Measurable sel)
    (f : I → ℝ) :
    (∫ x, f (sel x) ∂μ) = ∑ i, μ.real {x | sel x = i} * f i := by
  have hf : Integrable f (Measure.map sel μ) := Integrable.of_finite
  rw [← integral_map hsel.aemeasurable hf.aestronglyMeasurable, integral_fintype hf]
  apply Finset.sum_congr rfl
  intro i hi
  have hset : sel ⁻¹' {i} = {x | sel x = i} := by ext x; simp
  simp only [measureReal_def, Measure.map_apply hsel (measurableSet_singleton i),
    hset, smul_eq_mul]

/-- Every real-valued finite-selector function is integrable on a finite measure. -/
theorem integrable_selector {X I : Type*} [MeasurableSpace X]
    [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} [IsFiniteMeasure μ] {sel : X → I} (hsel : Measurable sel)
    (f : I → ℝ) : Integrable (fun x => f (sel x)) μ := by
  exact (Integrable.of_finite (f := f) (μ := Measure.map sel μ)).comp_measurable hsel

/-- A pointwise speed bound with a harmless factor of two. -/
theorem affine_sq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x v : H} {r R : ℝ} (hx : ‖x‖ ≤ R) :
    (inner ℝ x v + r) ^ 2 ≤ 2 * R ^ 2 * ‖v‖ ^ 2 + 2 * r ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hab : |inner ℝ x v| ≤ R * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x v).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ x v))
    (mul_nonneg hR (norm_nonneg v))).mpr hab
  rw [sq_abs, mul_pow] at hs
  nlinarith [sq_nonneg (inner ℝ x v - r)]

/-- Weighted cellwise integration of the time derivative of a finite affine maximum. -/
theorem integral_affine_speed_sq_le
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r : I → ℝ) {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hint : Integrable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) μ) :
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
      2 * R ^ 2 * (∑ i, μ.real {x | sel x = i} * ‖v i‖ ^ 2) +
        2 * (∑ i, μ.real {x | sel x = i} * r i ^ 2) := by
  calc
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
        ∫ x, 2 * R ^ 2 * ‖v (sel x)‖ ^ 2 + 2 * r (sel x) ^ 2 ∂μ := by
      apply integral_mono_ae hint (integrable_selector hsel
        (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2))
      exact hR.mono (fun x hx => affine_sq_le hx)
    _ = _ := by
      rw [integral_selector hsel (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2)]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        ring

/-- A bounded source and a measurable finite selector give the required square integrability. -/
theorem integrable_affine_speed_sq
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r : I → ℝ) {R : ℝ} (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    Integrable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) μ := by
  have hmeas : Measurable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) :=
    ((measurable_id.inner ((measurable_of_finite v).comp hsel)).add
      ((measurable_of_finite r).comp hsel)).pow_const 2
  apply (integrable_selector hsel
    (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2)).mono' hmeas.aestronglyMeasurable
  filter_upwards [hR] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (inner ℝ x (v (sel x)) + r (sel x)))] using
    (affine_sq_le (v := v (sel x)) (r := r (sel x)) hx)

/-- From the coupling and intercept energy bounds to the spatial potential speed bound.
The constant is non-sharp, which is sufficient for one-third stability. -/
theorem integral_affine_speed_sq_le_of_energy
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r m : I → ℝ) {R w k : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hm : ∀ i, μ.real {x | sel x = i} = m i)
    (hv : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hr : (∑ i, m i * r i ^ 2) ≤ k * R ^ 2 * w ^ 2) :
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
      2 * (1 + k) * R ^ 2 * w ^ 2 := by
  have h := integral_affine_speed_sq_le hsel v r hR
    (integrable_affine_speed_sq hsel v r hR)
  simp_rw [hm] at h
  calc
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
        2 * R ^ 2 * (∑ i, m i * ‖v i‖ ^ 2) + 2 * (∑ i, m i * r i ^ 2) := h
    _ ≤ 2 * R ^ 2 * w ^ 2 + 2 * (k * R ^ 2 * w ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hv (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

end Problem358.PotentialSpeed

end

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Problem358.FiniteMaxDerivative

variable {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X]

omit [Nonempty ι] in
/-- Selecting a measurable member of a finite measurable family stays measurable. -/
theorem measurable_selected (g : ι → X → ℝ) (k : X → ι)
    (hg : ∀ i, Measurable (g i)) (hk : ∀ i, MeasurableSet {x | k x = i}) :
    Measurable (fun x => g (k x) x) := by
  classical
  have h : Measurable (fun x => ∑ i, {x | k x = i}.indicator (g i) x) := by
    exact Finset.measurable_sum _ (fun i _ => (hg i).indicator (hk i))
  convert h using 1
  funext x
  simp [Set.indicator_apply]

/-- Endpoint values of the finite maximum are measurable. -/
theorem measurable_maxValue (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (maxValue f) := by
  have h : Measurable (Finset.univ.sup' Finset.univ_nonempty f) := by
    exact Finset.sup'_induction Finset.univ_nonempty f
      (p := fun g : X → ℝ => Measurable g)
      (fun g hg h hh => hg.sup hh) (fun i _ => hf i)
  convert h using 1
  funext x
  exact (Finset.sup'_apply Finset.univ_nonempty f x).symm

/-- A finite maximum inherits the spatial `L²` time bound from its active-branch speed.
All integrability and pointwise FTC obligations are discharged by measurability and uniform bounds. -/
theorem finite_max_path_L2_bound
    {μ : Measure X} [IsFiniteMeasure μ] {a b B D : ℝ} {L : ℝ≥0}
    (f g : ι → ℝ × X → ℝ) (k : ℝ × X → ι)
    (hab : a < b) (hB : 0 ≤ B)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hk : ∀ i, MeasurableSet {p | k p = i})
    (hLip : ∀ᵐ x ∂μ, ∀ i, LipschitzOnWith L (fun r => f i (r, x)) (Icc a b))
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ∀ i,
      HasDerivAt (fun r => f i (r, p.2)) (g i p) p.1)
    (hstrict : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ∀ j, j ≠ k p →
      f j p < f (k p) p)
    (hbound : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ‖g (k p) p‖ ≤ D)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc a b),
      (∫ x, g (k (r, x)) (r, x) ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (finiteMax (fun i => f i (b, x)) -
      finiteMax (fun i => f i (a, x))) ^ 2 ∂μ) ≤ B * (b - a) := by
  let u : ℝ → X → ℝ := fun r x => finiteMax (fun i => f i (r, x))
  let w : ℝ → X → ℝ := fun r x => g (k (r, x)) (r, x)
  have hwmeas : Measurable (Function.uncurry w) := measurable_selected g k hg hk
  have hw : Integrable (Function.uncurry w) ((volume.restrict (Ioc a b)).prod μ) :=
    Integrable.of_bound hwmeas.aestronglyMeasurable D hbound
  have hw2 : Integrable (fun p : ℝ × X => w p.1 p.2 ^ 2)
      ((volume.restrict (Ioc a b)).prod μ) := by
    apply Integrable.of_bound (hwmeas.pow_const 2).aestronglyMeasurable (D ^ 2)
    filter_upwards [hbound] with p hp
    change ‖g (k p) p ^ 2‖ ≤ D ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have humeas (r : ℝ) : Measurable (u r) := by
    exact measurable_maxValue (fun i x => f i (r, x))
      (fun i => (hf i).comp (measurable_const.prodMk measurable_id))
  have huLip : ∀ᵐ x ∂μ, LipschitzOnWith L (fun r => u r x) (Icc a b) := by
    filter_upwards [hLip] with x hx
    exact lipschitzOnWith_maxValue hx
  have hu2 : Integrable (fun x => (u b x - u a x) ^ 2) μ := by
    apply Integrable.of_bound ((humeas b).sub (humeas a) |>.pow_const 2).aestronglyMeasurable
      (((L : ℝ) * (b - a)) ^ 2)
    filter_upwards [huLip] with x hx
    have hh := hx.dist_le_mul b (right_mem_Icc.mpr hab.le) a (left_mem_Icc.mpr hab.le)
    have hh' : ‖u b x - u a x‖ ≤ (L : ℝ) * (b - a) := by
      simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hab), Real.norm_eq_abs] using hh
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hh' 2
  apply PotentialTimeIntegral.potential_path_L2_bound_of_lipschitz
    hab hB hw hw2 hu2
  · exact huLip.mono fun x hx => ⟨L, hx⟩
  · filter_upwards [hderiv, hstrict] with p hp hs
    exact hasDerivAt_of_strict_max (fun i => (hp i).continuousAt) hs (hp (k p))
  · exact hspeed

end Problem358.FiniteMaxDerivative

end

noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators

namespace Problem358

/-- Quantitative potential-path estimate from fixed cell masses, the coupling energy,
and the intercept energy. This is the time-integration step of finite-target stability. -/
theorem finite_potential_path_bound
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ]
    (u : ℝ → H → ℝ) (sel : ℝ → H → I) (v : I → H) (r : ℝ → I → ℝ) (m : I → ℝ)
    {s t R w k : ℝ} (hst : s < t) (hR : 0 ≤ R) (hw : 0 ≤ w) (hk : 0 ≤ k)
    (hxR : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hsel : ∀ q ∈ Ioc s t, Measurable (sel q))
    (hm : ∀ q ∈ Ioc s t, ∀ i, μ.real {x | sel q x = i} = m i)
    (hvEnergy : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioc s t, (∑ i, m i * r q i ^ 2) ≤ k * R ^ 2 * w ^ 2)
    (hInt : Integrable (fun p : ℝ × H =>
      inner ℝ p.2 (v (sel p.1 p.2)) + r p.1 (sel p.1 p.2))
      ((volume.restrict (Ioc s t)).prod μ))
    (hInt2 : Integrable (fun p : ℝ × H =>
      (inner ℝ p.2 (v (sel p.1 p.2)) + r p.1 (sel p.1 p.2)) ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hu : ∀ᵐ x ∂μ, ∃ L : ℝ≥0, LipschitzOnWith L (fun q => u q x) (Icc s t))
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc s t)).prod μ,
      HasDerivAt (fun q => u q p.2)
        (inner ℝ p.2 (v (sel p.1 p.2)) + r p.1 (sel p.1 p.2)) p.1) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤
      (Real.sqrt (2 * (1 + k)) * R * w) * (t - s) := by
  apply PotentialTimeIntegral.potential_path_L2_bound_of_lipschitz
    (v := fun q x => inner ℝ x (v (sel q x)) + r q (sel q x)) hst
    (by positivity) hInt hInt2 hu2 hu hderiv
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  have hbound := PotentialSpeed.integral_affine_speed_sq_le_of_energy
    (hsel q hq) v (r q) m hxR (hm q hq) hvEnergy (hrEnergy q hq)
  have hsq : (Real.sqrt (2 * (1 + k)) * R * w) ^ 2 =
      2 * (1 + k) * R ^ 2 * w ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]
  exact hbound

end Problem358

end

end OAI
