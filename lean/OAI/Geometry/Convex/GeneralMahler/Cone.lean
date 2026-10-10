import Mathlib

namespace OAI

/-!
# Positive dual cones and their Laplace integrals (paper Piece 2, §01)

The measure is ordinary Lebesgue (statements proved for any compatible
Lebesgue normalization where useful). "ProperCone" here is Mathlib's
closed cone containing zero; the extra paper hypotheses (solid and
contains no line) are imposed as needed. In the main application both
C and its positive dual have specified interior points.
-/

noncomputable section

open Filter Set MeasureTheory MeasureTheory.Measure Metric Real
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace

namespace GeneralMahler

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

section Cone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Paper C* = D. -/
abbrev posDual (C : ProperCone ℝ E) : ProperCone ℝ E :=
  ProperCone.innerDual (C : Set E)

@[simp]
theorem mem_posDual {C : ProperCone ℝ E} {x : E} :
    x ∈ posDual C ↔ (∀ ⦃y⦄, y ∈ C → 0 ≤ ⟪y, x⟫) := Iff.rfl

theorem interior_dual_bound {C : ProperCone ℝ E} {V : E}
    (hv : V ∈ interior (posDual C : Set E)) :
    ∃ c > 0, ∀ x ∈ C, c * ‖x‖ ≤ ⟪V, x⟫ := by
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hv)
  refine ⟨r, hr, fun x hx => ?_⟩
  by_cases h : x = 0
  · simp [h]
  have hxp := norm_pos_iff.mpr h
  have hm : V - (r / ‖x‖) • x ∈ closedBall V r := by
    rw [mem_closedBall, dist_eq_norm, sub_right_comm, sub_self, zero_sub,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hxp)]
    exact le_of_eq (div_mul_cancel₀ _ hxp.ne')
  have hi := mem_posDual.mp (hb hm) hx
  rwa [real_inner_comm, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, pow_two, ← mul_assoc, div_mul_cancel₀ _ hxp.ne',
    sub_nonneg] at hi

theorem interior_dual_of_bound {C : ProperCone ℝ E} {V : E}
    {c : ℝ} (hc : 0 < c) (hf : ∀ x ∈ C, c * ‖x‖ ≤ ⟪V, x⟫) :
    V ∈ interior (posDual C : Set E) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply nhds_basis_closedBall.mem_iff.mpr
  refine ⟨c, hc, ?_⟩
  intro y hy
  apply mem_posDual.mpr
  intro x hx
  have h₁ := hf x hx
  have h₂ := real_inner_le_norm (V - y) x
  rw [inner_sub_left] at h₂
  rw [real_inner_comm]
  have hle : ‖V - y‖ ≤ c := by rwa [mem_closedBall, dist_comm, dist_eq_norm] at hy
  have h₃ := mul_le_mul_of_nonneg_right hle (norm_nonneg x)
  linarith

/-- If y is not interior to the dual, then there is a nonzero bad
direction in the cone. -/
theorem exists_ray_of_not_interior_dual {C : ProperCone ℝ E} {y : E}
    (h : y ∉ interior (posDual C : Set E)) :
    ∃ x ∈ C, ‖x‖ = 1 ∧ ⟪y, x⟫ ≤ 0 := by
  let s := (C : Set E) ∩ sphere 0 1
  by_contra! hn
  have hc : ∃ c > 0, ∀ x ∈ s, c ≤ ⟪y, x⟫ := by
    rcases s.eq_empty_or_nonempty with hs|hs
    · exact ⟨1, by norm_num, by simp [hs]⟩
    · have hk : IsCompact s :=
        (isCompact_sphere (0 : E) 1).inter_left C.isClosed
      obtain ⟨x, hx, hf⟩ := hk.exists_isMinOn hs
        (by fun_prop : ContinuousOn (fun z => ⟪y, z⟫) s)
      exact ⟨⟪y, x⟫, hn _ hx.1 (by simpa using hx.2), fun _ hb => hf hb⟩
  obtain ⟨c,hc,hb⟩ := hc
  apply h
  apply interior_dual_of_bound hc
  intro x hx
  by_cases hz : x = 0
  · simp [hz]
  have hp := norm_pos_iff.mpr hz
  have hm : ‖x‖⁻¹ • x ∈ s := by
    refine ⟨C.smul_mem hx (inv_nonneg.mpr hp.le), ?_⟩
    simp [norm_smul, hp.ne']
  specialize hb _ hm
  rwa [real_inner_smul_right, ← div_eq_inv_mul, le_div_iff₀ hp] at hb

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

/-- Paper §01 χ_C(V). Used with V interior to the dual. -/
def chi (C : ProperCone ℝ E) (V : E) : ℝ :=
  ∫ x in C, Real.exp (-⟪V,x⟫)

/-- For limiting arguments keep track of infinity. -/
def chiExt (C : ProperCone ℝ E) (V : E) : ℝ≥0∞ :=
  ∫⁻ x in C, ENNReal.ofReal (Real.exp (-⟪V,x⟫))

/-- Exponential tail with polynomial factors, finiteness.
This elementary proof uses the integrable comparison (1+‖x‖)^(-r)
above dimension r>n. -/
theorem integrable_polynomial_exp_tail {c : ℝ} (hc : 0 < c) (p : ℕ) :
    Integrable (fun x : E => (1 + ‖x‖)^p * Real.exp (-(c * ‖x‖))) := by
  let r : ℝ := (Module.finrank ℝ E : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a := c / ((p:ℝ)+r)
  have har : 0 < (p:ℝ)+r := by positivity
  have ha : 0 < a := div_pos hc har
  let k := ((p:ℝ)+r) * (a - 1 - Real.log a)
  refine ((integrable_one_add_norm (show (Module.finrank ℝ E:ℝ)<r by
    dsimp [r]; linarith)).const_mul (Real.exp k)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  set b := (1 + ‖x‖)
  have hb : 0 < b := by dsimp [b]; positivity
  have H : Real.log b ≤ a*b - 1 - Real.log a := by
    have he := Real.log_le_sub_one_of_pos (mul_pos ha hb)
    rwa [Real.log_mul ha.ne' hb.ne', add_comm, ← le_sub_iff_add_le] at he
  have eqc : ((p:ℝ)+r)*a = c := by
    rw [mul_comm]; exact div_mul_cancel₀ _ har.ne'
  have H₂ : Real.log b * p - c * ‖x‖ ≤ k + Real.log b * (-r) := by
    calc
      _ = ((p:ℝ)+r) * Real.log b + Real.log b * (-r) - c * ‖x‖ := by ring
      _ ≤ ((p:ℝ)+r) * (a*b - 1 - Real.log a) + Real.log b * (-r) - c * ‖x‖ := by gcongr
      _ = k + Real.log b * (-r) := by
        dsimp [k,b]
        rw [← eqc]
        ring
  change ‖b^p * Real.exp _‖ ≤ Real.exp k * b ^ (-r)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_natCast, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, ← sub_eq_add_neg]
  exact H₂

theorem chi_integrable {C : ProperCone ℝ E} {V : E}
    (hV : V ∈ interior (posDual C : Set E)) :
    IntegrableOn (fun x => Real.exp (-⟪V,x⟫)) C := by
  obtain ⟨c,hc,hb⟩ := interior_dual_bound hV
  have htail : Integrable (fun x : E => Real.exp (-(c*‖x‖))) := by
    simpa using (integrable_polynomial_exp_tail (E := E) hc 0)
  apply htail.integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem C.isClosed.measurableSet] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp,
    neg_le_neg_iff] using hb x hx

theorem chi_pos {C : ProperCone ℝ E} (hs : (interior (C:Set E)).Nonempty)
    {V : E} (hV : V ∈ interior (posDual C : Set E)) :
    0 < chi C V := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?hn (chi_integrable hV)).mpr
  case hn => exact ae_of_all _ fun x => (Real.exp_pos _).le
  apply lt_of_lt_of_le (isOpen_interior.measure_pos volume hs)
  apply measure_mono
  exact fun x hx => ⟨(Real.exp_pos _).ne', interior_subset hx⟩

theorem chiExt_eq {C : ProperCone ℝ E} {V : E}
    (hV : V ∈ interior (posDual C : Set E)) :
    chiExt C V = ENNReal.ofReal (chi C V) :=
  (ofReal_integral_eq_lintegral_ofReal (chi_integrable hV)
    (ae_of_all _ fun _x => (Real.exp_pos _).le)).symm

omit [IsAddHaarMeasure (volume : Measure E)] in
theorem chiExt_lsc (C : ProperCone ℝ E) : LowerSemicontinuous (chiExt C) := by
  intro V b hlt
  let g (u x : E) := ENNReal.ofReal (Real.exp (-⟪u,x⟫))
  refine eventually_lt_of_lt_liminf ?_
  refine hlt.trans_le (le_trans ?_ (lintegral_liminf_le
    (u := 𝓝 V) (μ := volume.restrict (C : Set E)) (f := g) (by intro i; dsimp [g]; fun_prop)))
  apply lintegral_mono
  intro x
  have hf : Continuous (fun i => g i x) := ENNReal.continuous_ofReal.comp (show Continuous (fun i => Real.exp (-⟪i,x⟫)) by fun_prop)
  exact (Tendsto.liminf_eq (hf.tendsto V)).symm.le

/-- If w has a bad direction in C, then the Laplace integral
is infinite: translate C along that ray. The translated copy
does not decrease the integral but misses a relatively low layer
of positive volume measured in any interior-dual direction. -/
theorem chiExt_top {C : ProperCone ℝ E}
    (hs : (interior (C : Set E)).Nonempty)
    (hd : (interior (posDual C : Set E)).Nonempty)
    {V : E} (hV : V ∉ interior (posDual C : Set E)) :
    chiExt C V = ∞ := by
  obtain ⟨q,hq,hq1,hq2⟩ := exists_ray_of_not_interior_dual hV
  obtain ⟨a,ha⟩ := hs
  obtain ⟨W,hW⟩ := hd
  obtain ⟨c,hc,hcw⟩ := interior_dual_bound hW
  have hq3 : 0 < ⟪W,q⟫ := by simpa only [hq1,mul_one] using (lt_of_lt_of_le
    (mul_pos hc (by rw [hq1]; norm_num)) (hcw q hq))
  let r := max 0 ⟪W,a⟫ / ⟪W,q⟫ + 1
  have hrp : 0 ≤ (max 0 ⟪W,a⟫) / ⟪W,q⟫ := div_nonneg (le_max_left ..) hq3.le
  have hr : 0 < r := by dsimp [r]; linarith
  let p := r • q
  have hp : p ∈ C := C.smul_mem hq hr.le
  have hpa : ⟪W,a⟫ < ⟪W,p⟫ := by
    dsimp [p, r]
    rw [real_inner_smul_right, add_mul, div_mul_cancel₀ _ hq3.ne', one_mul]
    exact lt_of_le_of_lt (le_max_right ..) (by linarith)
  let D : Set E := {x | x - p ∈ C}
  let B := interior (C : Set E) ∩ {x | ⟪W,x⟫ < ⟪W,p⟫}
  have hm : MeasurableSet D :=
    ((C.isClosed).preimage (continuous_id.sub continuous_const)).measurableSet
  have hbo : IsOpen B := isOpen_interior.inter
    (isOpen_lt (by fun_prop) continuous_const)
  have hdis : Disjoint D B := Set.disjoint_left.mpr (by
    intro x hx hy
    have hxu := hcw (x - p) hx
    rw [inner_sub_right] at hxu
    have hh : ⟪W,x⟫ < ⟪W,p⟫ := hy.2
    have hh' : 0 ≤ c * ‖x - p‖ := by positivity
    linarith)
  have hsub : D ∪ B ⊆ C := union_subset (fun x hx => by
    have hh := C.add_mem hx hp
    rwa [sub_add_cancel] at hh) (inter_subset_left.trans interior_subset)
  let g (x : E) := ENNReal.ofReal (Real.exp (-⟪V,x⟫))
  have gm : Measurable g := by fun_prop (disch := aesop)
  have hpos : 0 < ∫⁻ x in B, g x := by
    apply (lintegral_pos_iff_support gm).mpr
    have hh : Function.support g = univ := eq_univ_of_forall (fun x =>
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    rw [hh, Measure.restrict_apply_univ]
    exact hbo.measure_pos volume ⟨a,ha,hpa⟩
  have hle : chiExt C V ≤ ∫⁻ x in D, g x := by
    have hme := measurePreserving_add_right volume p
    rw [← hme.map_eq, setLIntegral_map hm gm hme.measurable]
    -- The preimage is exactly C
    have heq : (fun x => x + p) ⁻¹' D = C := by ext; simp [D]
    rw [heq]
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [inner_add_right]
    have hu : ⟪V,p⟫ ≤ 0 := by
      dsimp [p]
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hr.le hq2
    linarith
  by_contra hh
  have halt : chiExt C V + (∫⁻ x in B, g x) ≤ chiExt C V := calc
    _ ≤ (∫⁻ x in D, g x) + (∫⁻ x in B, g x) := add_le_add_left hle _
    _ = ∫⁻ x in D ∪ B, g x := (lintegral_union hbo.measurableSet hdis).symm
    _ ≤ _ := lintegral_mono_set hsub
  exact (not_lt_of_ge halt) (ENNReal.lt_add_right hh hpos.ne')

/-- Strict convexity on dual interior for a solid cone. -/
theorem chi_strictConvex {C : ProperCone ℝ E}
    (hs : (interior (C : Set E)).Nonempty) :
    StrictConvexOn ℝ (interior (posDual C : Set E)) (chi C) := by
  have cv := (posDual C).convex.interior
  refine ⟨cv, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let z := a • x + b • y
  have hz := cv hx hy ha.le hb.le hab
  let f (u t : E) := Real.exp (-⟪u,t⟫)
  let g (t : E) := a * f x t + b * f y t - f z t
  have hi : IntegrableOn g C :=
    (((chi_integrable hx).const_mul _).add ((chi_integrable hy).const_mul _)).sub (chi_integrable hz)
  have hn : ∀ t, 0 ≤ g t := by
    intro t
    have H := strictConvexOn_exp.convexOn.2
      (show -⟪x,t⟫ ∈ univ from mem_univ _) (show -⟪y,t⟫ ∈ univ from mem_univ _)
      ha.le hb.le hab
    apply sub_nonneg.mpr
    simpa [f,z, inner_add_left, real_inner_smul_left, neg_add, add_comm] using H
  let B : Set E := interior (C : Set E) ∩ {t | ⟪x-y,t⟫ ≠ 0}
  have hbo : IsOpen B := isOpen_interior.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  obtain ⟨u,hu⟩ := hs
  have hu₁ : 0 < ⟪x-y,x-y⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hxy)
  have hbne : B.Nonempty := by
    by_cases h : ⟪x-y,u⟫ = 0
    · let w : ℝ → E := fun s => u + s • (x-y)
      have hw : Continuous w := by fun_prop (disch := aesop)
      obtain ⟨s,hs,hh⟩ : ∃ s, 0 < s ∧ w s ∈ interior (C : Set E) := by
        have hne : w ⁻¹' interior (C : Set E) ∈ 𝓝 (0:ℝ) :=
          (hw.tendsto 0) (isOpen_interior.mem_nhds (by simpa [w] using hu))
        exact ((show ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s from self_mem_nhdsWithin).and
          ((nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) hne)).exists
      refine ⟨w s, hh, ?_⟩
      change ⟪x-y,u+s • (x-y)⟫ ≠ 0
      simp [inner_add_right, real_inner_smul_right, h, hs.ne', sub_ne_zero.mpr hxy]
    · exact ⟨u, hu, h⟩
  have hpos : 0 < ∫ t in C, g t := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hn) hi).mpr
    refine lt_of_lt_of_le (hbo.measure_pos volume hbne) (measure_mono (fun t ht => ?_))
    refine ⟨?_, interior_subset ht.1⟩
    apply ne_of_gt
    have HH : -⟪x,t⟫ ≠ -⟪y,t⟫ := by
      have h : ⟪x-y,t⟫ ≠ 0 := ht.2
      simpa [sub_ne_zero,inner_sub_left] using h
    have H := strictConvexOn_exp.2 (mem_univ _) (mem_univ _) HH ha hb hab
    apply sub_pos.mpr
    simpa [f,z, inner_add_left, real_inner_smul_left, neg_add, add_comm] using H
  change 0 < ∫ t in C, (a * f x t + b * f y t - f z t) at hpos
  rw [integral_sub, integral_add, integral_const_mul, integral_const_mul] at hpos
  · exact sub_pos.mp hpos
  all_goals
    first
    | exact chi_integrable hz
    | exact (chi_integrable hx).const_mul _
    | exact (chi_integrable hy).const_mul _
    | exact ((chi_integrable hx).const_mul _).add ((chi_integrable hy).const_mul _)

end Cone
end GeneralMahler

end

end OAI
