import OAI.Geometry.PolarProducts.GalerkinBounds

namespace OAI

universe u114 u115

section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem integral_sq_le (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    simp
  let avg := ∫ t in a..b, f t
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hnon : 0 ≤ ∫ t in a..b, (L*f t-avg)^2 :=
    integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  have he (t : ℝ) : (L*f t-avg)^2 = L^2*(f t)^2-(2*L*avg)*f t+avg^2 := by ring
  simp_rw [he] at hnon
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const] at hnon
  · simp only [smul_eq_mul] at hnon
    change 0 ≤ L^2*(∫ t in a..b, (f t)^2)-(2*L*avg)*avg+L*avg^2 at hnon
    change avg^2 ≤ L*(∫ t in a..b, (f t)^2)
    nlinarith
  · exact (hf.pow 2).intervalIntegrable _ _ |>.const_mul _
  · exact hf.intervalIntegrable _ _ |>.const_mul _
  · exact (((hf.pow 2).const_mul _).sub (hf.const_mul _)).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem norm_sub_sq_le (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {a b : ℝ} (hab : a ≤ b) :
    ‖x b-x a‖^2 ≤ (b-a)*(∫ t in a..b, ‖v t‖^2) := by
  have he := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)
  have hn : ‖x b-x a‖ ≤ ∫ t in a..b, ‖v t‖ := by
    rw [← he]
    exact norm_integral_le_integral_norm hab
  have hi := integral_sq_le (fun t => ‖v t‖) hv.norm hab
  have hs : ‖x b-x a‖^2 ≤ (∫ t in a..b, ‖v t‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hs.trans hi

 theorem norm_sub_sq_le_global (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {D : ℝ}
    (hD : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ‖x b-x a‖^2 ≤ D^2*|b-a| := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    rwa [norm_sub_rev, abs_sub_comm] at h
  have hi := integral_mono_interval (μ := volume) ha.1 hab hb.2
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) ((hv.norm.pow 2).intervalIntegrable 0 1)
  have hc := norm_sub_sq_le x v hv hd hab
  have hm := mul_le_mul_of_nonneg_left (hi.trans hD) (sub_nonneg.mpr hab)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact hc.trans (by nlinarith)

 theorem norm_bound (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hxm : (∫ t in (0:ℝ)..1, ‖x t‖^2) ≤ A^2)
    (hvm : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ A+D := by
  have hx : Continuous x := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hpoint (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ ‖x s‖+D := by
    have hdiff := norm_sub_sq_le_global x v hv hd hvm hs ht
    have hab : |t-s| ≤ 1 := (abs_le).mpr ⟨by linarith [ht.1,hs.2], by linarith [ht.2,hs.1]⟩
    have hmul := mul_le_mul_of_nonneg_left hab (sq_nonneg D)
    have hn : ‖x t-x s‖ ≤ D := by nlinarith [norm_nonneg (x t-x s)]
    have htri := norm_sub_le (x t-x s) (-x s)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    linarith
  have hi : ∫ s in (0:ℝ)..1, ‖x t‖ ≤ ∫ s in (0:ℝ)..1, ‖x s‖+D :=
    integral_mono_on (by norm_num) intervalIntegrable_const
      ((hx.norm.add continuous_const).intervalIntegrable _ _) hpoint
  rw [integral_const, integral_add (hx.norm.intervalIntegrable _ _) intervalIntegrable_const,
    integral_const] at hi
  simp only [sub_zero, one_smul] at hi
  have hcs := integral_sq_le (fun s => ‖x s‖) hx.norm (show (0:ℝ) ≤ 1 by norm_num)
  simp only [sub_zero, one_mul] at hcs
  have hmean : ∫ t_1 in (0:ℝ)..1, ‖x t_1‖ ≤ A := by
    nlinarith [integral_nonneg_of_forall (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) (fun s => norm_nonneg (x s))]
  linarith

abbrev Segment := Icc (0 : ℝ) 1

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem exists_subsequence [ProperSpace E] (u : ℕ → C(Segment,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n t) (u n s)^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n t‖ ≤ R) :
    ∃ x : C(Segment,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  let eqv := ContinuousMap.isometryEquivBoundedOfCompact Segment E
  let v : ℕ → (Segment →ᵇ E) := fun n => eqv (u n)
  have heq : Equicontinuous ((↑) : Set.range v → Segment → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε^2/(D^2+1), by positivity, fun t s hts f => ?_⟩
    rcases f.property with ⟨n,hn⟩
    have hm := hmod n t s
    have hd : (D^2+1)*dist t s < ε^2 := by
      have := (lt_div_iff₀ (by positivity : 0 < D^2+1)).mp hts
      linarith
    rw [← hn]
    change dist (u n t) (u n s) < ε
    nlinarith [(dist_nonneg : 0 ≤ dist (u n t) (u n s)), (dist_nonneg : 0 ≤ dist t s)]
  have hc : IsCompact (closure (Set.range v)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:E) R)
      (isCompact_closedBall _ _) (Set.range v)
      (fun f t hf => by
        rcases hf with ⟨n,rfl⟩
        change dist (u n t) (0:E) ≤ R
        simpa only [dist_zero_right] using hbound n t) heq
  obtain ⟨x,hx,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨eqv.symm x,φ,hφ,?_⟩
  exact eqv.symm.continuous.continuousAt.tendsto.comp ht

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)

def restriction (x : C(Time,E)) : C(Segment,E) :=
  ⟨fun t => x (t.val : Time), x.continuous.comp (continuous_quot_mk.comp continuous_subtype_val)⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem restriction_isometry : Isometry (restriction (E := E)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist x y)).2
    intro t
    exact ContinuousMap.dist_apply_le_dist (t.val : Time)
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist (restriction x) (restriction y))).2
    intro t
    let r := AddCircle.equivIoc (1 : ℝ) 0 t
    have hr : r.val ∈ Set.Icc (0:ℝ) 1 := ⟨r.property.1.le, by simpa using r.property.2⟩
    have h := ContinuousMap.dist_apply_le_dist (f := restriction x) (g := restriction y) ⟨r.val,hr⟩
    simpa only [restriction, ContinuousMap.coe_mk, r, AddCircle.coe_equivIoc] using h

omit [NormedSpace ℝ E] in
 theorem exists_periodic_subsequence [ProperSpace E] (u : ℕ → C(Time,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n (t.val : Time)) (u n (s.val : Time))^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n (t.val : Time)‖ ≤ R) :
    ∃ x : C(Time,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  obtain ⟨x,φ,hφ,ht⟩ := exists_subsequence (fun n => restriction (u n)) hmod hbound
  have hc' : Cauchy (Filter.map restriction (Filter.map (u ∘ φ) Filter.atTop)) := by
    rw [Filter.map_map]
    exact ht.cauchySeq
  have hc : CauchySeq (u ∘ φ) :=
    restriction_isometry.isUniformInducing.cauchy_map_iff.mp hc'
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y,φ,hφ,hy⟩

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)
abbrev μ : Measure Time := AddCircle.haarAddCircle
open FourierPolynomial (integrable_continuous)

 def coefficient (n : ℤ) : C(Time,ℂ) →L[ℂ] ℂ := by
  let L : C(Time,ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => fourierCoeff f n
    map_add' := fun f g => congrFun (fourierCoeff.add
      (integrable_continuous f.continuous) (integrable_continuous g.continuous)) n
    map_smul' := fun c f => fourierCoeff.const_smul f c n }
  apply L.mkContinuous 1
  intro f
  change ‖∫ t : Time, fourier (-n) t • f t ∂μ‖ ≤ 1*‖f‖
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖f‖)
    (Filter.Eventually.of_forall (fun t : Time => show ‖fourier (-n) t • f t‖ ≤ ‖f‖ by
      simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using f.norm_coe_le_norm t))
  simpa using h

@[simp] theorem coefficient_apply (n : ℤ) (f : C(Time,ℂ)) : coefficient n f = fourierCoeff f n := rfl

 theorem coefficient_ext {f g : C(Time,ℂ)} (h : ∀ n, coefficient n f = coefficient n g) : f = g := by
  have hz (n : ℤ) : fourierCoeff (f-g) n = 0 := by
    change coefficient n (f-g) = 0
    rw [map_sub, h, sub_self]
  have hs : Summable (fourierCoeff (f-g)) := by
    simpa only [funext hz] using (summable_zero : Summable (fun _ : ℤ => (0:ℂ)))
  have hh := hasSum_fourier_series_of_summable hs
  simp only [hz, zero_smul] at hh
  have he : f-g = 0 := hh.unique hasSum_zero
  exact sub_eq_zero.mp he

 theorem coefficient_const (n : ℤ) (c : ℂ) :
    coefficient n (ContinuousMap.const Time c) = if n = 0 then c else 0 := by
  rw [coefficient_apply, fourierCoeff]
  simp only [ContinuousMap.coe_const, Function.const_apply, smul_eq_mul]
  rw [integral_mul_const, FourierPolynomial.integral_fourier]
  simp only [neg_eq_zero]
  split_ifs <;> simp

 theorem constant_of_nonzero_coeff {f : C(Time,ℂ)}
    (h : ∀ n : ℤ, n ≠ 0 → coefficient n f = 0) :
    f = ContinuousMap.const Time (coefficient 0 f) := by
  apply coefficient_ext
  intro n
  rw [coefficient_const]
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn,h n hn]

 theorem continuous_lift {E : Type u115} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous f) (hp : Function.Periodic f 1) : Continuous hp.lift :=
  hf.quotient_liftOn' _

 def primitive (v : C(Time,ℂ)) (t : ℝ) : ℂ := ∫ s in (0:ℝ)..t, v (s : Time)

 theorem hasDerivAt_primitive (v : C(Time,ℂ)) (t : ℝ) :
    HasDerivAt (primitive v) (v (t : Time)) t := by
  have hv : Continuous (fun s : ℝ => v (s : Time)) := v.continuous.comp continuous_quot_mk
  exact intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _) hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

 theorem periodic_primitive (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) :
    Function.Periodic (primitive v) 1 := by
  have hv : Continuous (fun s : ℝ => v (s : Time)) := v.continuous.comp continuous_quot_mk
  have hp : Function.Periodic (fun s : ℝ => v (s : Time)) 1 := by
    intro t
    simp
  have hi : ∫ s in (0:ℝ)..1, v (s : Time) = 0 := by
    have h := hzero
    rw [coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0] at h
    simpa only [one_div_one, one_smul, zero_add, neg_zero, fourier_zero] using h
  intro t
  unfold primitive
  rw [hp.intervalIntegral_add_eq_add 0 t (fun a b => hv.intervalIntegrable a b)]
  simp only [zero_add, hi, add_zero]

 def periodicPrimitive (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) : C(Time,ℂ) :=
  ⟨(periodic_primitive v hzero).lift,
    continuous_lift (continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_primitive v t).continuousAt)) _⟩

@[simp] theorem periodicPrimitive_coe (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) (t : ℝ) :
    periodicPrimitive v hzero (t : Time) = primitive v t := rfl

 theorem coefficient_eq_on (f : C(Time,ℂ)) (n : ℤ) :
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun t : ℝ => f (t : Time)) n = coefficient n f := by
  rw [fourierCoeffOn_eq_integral, coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp

 theorem derivative_coefficient (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0)
    {n : ℤ} (hn : n ≠ 0) :
    (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) * coefficient n (periodicPrimitive v hzero) = coefficient n v := by
  have hp := periodic_primitive v hzero
  have hi := fourierCoeffOn_of_hasDerivAt (show (0:ℝ) < 1 by norm_num) hn
    (fun t _ => hasDerivAt_primitive v t)
    ((v.continuous.comp continuous_quot_mk).intervalIntegrable 0 1)
  have ht : primitive v 1 = primitive v 0 := by simpa using hp 0
  simp only [ht, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul, zero_sub] at hi
  change fourierCoeffOn _ (fun t : ℝ => periodicPrimitive v hzero (t : Time)) n =
    1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * -fourierCoeffOn _ (fun t : ℝ => v (t : Time)) n at hi
  rw [coefficient_eq_on, coefficient_eq_on] at hi
  rw [hi]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

 theorem hasDerivAt_of_coefficients (x v : C(Time,ℂ))
    (h : ∀ n : ℤ, coefficient n v = (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*coefficient n x)
    (t : ℝ) : HasDerivAt (fun s : ℝ => x (s : Time)) (v (t : Time)) t := by
  have hz : coefficient 0 v = 0 := by simpa using h 0
  let y := periodicPrimitive v hz
  have hc : x-y = ContinuousMap.const Time (coefficient 0 (x-y)) := by
    apply constant_of_nonzero_coeff
    intro n hn
    rw [map_sub]
    have he := derivative_coefficient v hz hn
    rw [h n] at he
    have hn' : (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      exact_mod_cast hn
    have heq := (mul_left_cancel₀ hn') he
    change coefficient n x-coefficient n (periodicPrimitive v hz) = 0
    exact sub_eq_zero.mpr heq.symm
  have hx (s : ℝ) : x (s : Time) = primitive v s+coefficient 0 (x-y) := by
    have he := congrArg (fun f : C(Time,ℂ) => f (s : Time)) hc
    change x (s : Time)-primitive v s = coefficient 0 (x-y) at he
    exact sub_eq_iff_eq_add'.mp he
  simpa only [← hx] using (hasDerivAt_primitive v t).add_const (coefficient 0 (x-y))

end
end PeriodicFourier

end NonsqueezingInline

end OAI
