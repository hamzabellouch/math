import OAI.Analysis.HenonEmden.SpatialComponents

namespace OAI

section Intervals
open MeasureTheory Set Filter Topology
namespace HenonLaneEmden.IntervalGeometry


/-- Integral over the segment of half-length `r` centered at `x`. -/
noncomputable def segmentIntegral (k : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ t in x - r..x + r, k t

lemma primitive_hasDerivAt {k : ℝ → ℝ} (hk : Continuous k) (x : ℝ) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, k t) (k x) x :=
  intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt

lemma segmentIntegral_eq_primitive {k : ℝ → ℝ} (hk : Continuous k) (r x : ℝ) :
    segmentIntegral k r x = (∫ t in (0 : ℝ)..x + r, k t) -
      (∫ t in (0 : ℝ)..x - r, k t) := by
  unfold segmentIntegral
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hk.intervalIntegrable (μ := volume) 0 (x - r)) (hk.intervalIntegrable (x - r) (x + r))
  linarith

lemma segmentIntegral_hasDerivAt {k : ℝ → ℝ} (hk : Continuous k) (r x : ℝ) :
    HasDerivAt (segmentIntegral k r) (k (x + r) - k (x - r)) x := by
  have h₁ := (primitive_hasDerivAt hk (x + r)).comp x ((hasDerivAt_id x).add_const r)
  have h₂ := (primitive_hasDerivAt hk (x - r)).comp x ((hasDerivAt_id x).sub_const r)
  have heq : segmentIntegral k r = (fun y =>
      (∫ t in (0 : ℝ)..y + r, k t) - (∫ t in (0 : ℝ)..y - r, k t)) :=
    funext (segmentIntegral_eq_primitive hk r)
  rw [heq]
  convert h₁.sub h₂ using 1 <;> first | rfl | simp only [mul_one]

lemma segmentIntegral_continuous {k : ℝ → ℝ} (hk : Continuous k) (r : ℝ) :
    Continuous (segmentIntegral k r) :=
  continuous_iff_continuousAt.mpr (fun x => (segmentIntegral_hasDerivAt hk r x).continuousAt)

lemma segmentIntegral_even {k : ℝ → ℝ} (heven : ∀ x, k (-x) = k x) (r x : ℝ) :
    segmentIntegral k r (-x) = segmentIntegral k r x := by
  unfold segmentIntegral
  have h := intervalIntegral.integral_comp_neg (a := x-r) (b := x+r) k
  simp only [heven] at h
  rw [show -x - r = -(x + r) by ring, show -x + r = -(x - r) by ring]
  exact h.symm

lemma segmentIntegral_antitoneOn {k : ℝ → ℝ} (hk : Continuous k)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x) {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn (segmentIntegral k r) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (segmentIntegral_continuous hk r).continuousOn
  · exact fun x _ => (segmentIntegral_hasDerivAt hk r x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(segmentIntegral_hasDerivAt hk r x).deriv]
    apply sub_nonpos.mpr
    apply hanti
    have hx' : 0 ≤ x := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hx)
    rw [abs_of_nonneg (add_nonneg hx' hr)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma segmentIntegral_abs {k : ℝ → ℝ} (heven : ∀ x, k (-x) = k x) (r x : ℝ) :
    segmentIntegral k r |x| = segmentIntegral k r x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx]
    exact segmentIntegral_even heven r x

lemma segmentIntegral_antitone_abs {k : ℝ → ℝ} (hk : Continuous k)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {r : ℝ} (hr : 0 ≤ r) {x y : ℝ} (hxy : |x| ≤ |y|) :
    segmentIntegral k r y ≤ segmentIntegral k r x := by
  rw [← segmentIntegral_abs heven r y, ← segmentIntegral_abs heven r x]
  exact segmentIntegral_antitoneOn hk hanti hr (abs_nonneg x) (abs_nonneg y) hxy

lemma integral_translate_eq_segment (k : ℝ → ℝ) (c d x : ℝ) :
    (∫ y in c..d, k (x - y)) =
      segmentIntegral k ((d-c)/2) (x-(c+d)/2) := by
  rw [intervalIntegral.integral_comp_sub_left]
  unfold segmentIntegral
  congr 1 <;> ring

/-- The drift of the two interval midpoints has the opposite sign to the
    integrated endpoint difference of a symmetric decreasing kernel. -/
lemma midpoint_endpoint_sign {k : ℝ → ℝ} (hk : Continuous k)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((a+b)/2-(c+d)/2) * (∫ y in c..d, (k (b-y)-k (a-y))) ≤ 0 := by
  have hkb : Continuous (fun y : ℝ => k (b-y)) := hk.comp (continuous_const.sub continuous_id)
  have hka : Continuous (fun y : ℝ => k (a-y)) := hk.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_sub (hkb.intervalIntegrable c d) (hka.intervalIntegrable c d)]
  rw [integral_translate_eq_segment k c d b, integral_translate_eq_segment k c d a]
  have hr : 0 ≤ (d-c)/2 := by linarith
  rcases le_or_gt 0 ((a+b)/2-(c+d)/2) with hm | hm
  · apply mul_nonpos_of_nonneg_of_nonpos hm
    apply sub_nonpos.mpr
    apply segmentIntegral_antitone_abs hk heven hanti hr
    rw [← sq_le_sq]
    nlinarith
  · apply mul_nonpos_of_nonpos_of_nonneg hm.le
    apply sub_nonneg.mpr
    apply segmentIntegral_antitone_abs hk heven hanti hr
    rw [← sq_le_sq]
    nlinarith




/-- Restricted Newton kernel; `c` is its (positive) normalization. -/
noncomputable def kernel (n : ℕ) (l c h : ℝ) : ℝ :=
  c * (l ^ 2 + h ^ 2) ^ ((2 - (n : ℝ)) / 2)

lemma base_pos {l : ℝ} (hl : 0 < l) (x : ℝ) : 0 < l ^ 2 + x ^ 2 := by
  positivity

lemma kernel_nonneg (n : ℕ) {l c : ℝ} (hc : 0 ≤ c) (h : ℝ) :
    0 ≤ kernel n l c h := by
  unfold kernel
  positivity

lemma kernel_even (n : ℕ) (l c h : ℝ) : kernel n l c (-h) = kernel n l c h := by
  simp [kernel]

lemma kernel_continuous (n : ℕ) {l : ℝ} (hl : 0 < l) (c : ℝ) :
    Continuous (kernel n l c) := by
  apply continuous_const.mul
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun x => Or.inl (ne_of_gt (base_pos hl x)))

lemma kernel_hasDerivAt (n : ℕ) {l : ℝ} (hl : 0 < l) (c h : ℝ) :
    HasDerivAt (kernel n l c)
      (-((n : ℝ) - 2) * h / (l ^ 2 + h ^ 2) * kernel n l c h) h := by
  have hd := ((((hasDerivAt_id h).pow 2).const_add (l ^ 2)).rpow_const (p := (2 - (n : ℝ)) / 2)
    (Or.inl (ne_of_gt (base_pos hl h)))).const_mul c
  convert hd using 1 <;> try rfl
  simp only [kernel, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, Real.rpow_sub (base_pos hl h), Real.rpow_one]
  field_simp
  ring

lemma kernel_antitone_abs (n : ℕ) (hn : 3 ≤ n) {l c : ℝ} (hl : 0 < l)
    (hc : 0 ≤ c) {x y : ℝ} (hxy : |x| ≤ |y|) : kernel n l c y ≤ kernel n l c x := by
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.rpow_le_rpow_of_nonpos (base_pos hl x)
  · have hsq : x ^ 2 ≤ y ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hxy 2
    linarith
  · have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith




noncomputable def boxIntegral (a b c d : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, F x y

lemma boxIntegral_congr (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (h : ∀ x y, F x y = G x y) : boxIntegral a b c d F = boxIntegral a b c d G := by
  have heq : F = G := funext (fun x => funext (h x))
  rw [heq]

lemma boxIntegral_add (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry) :
    boxIntegral a b c d (fun x y => F x y + G x y) =
      boxIntegral a b c d F + boxIntegral a b c d G := by
  unfold boxIntegral
  simp_rw [intervalIntegral.integral_add
    ((hF.uncurry_left _).intervalIntegrable c d) ((hG.uncurry_left _).intervalIntegrable c d)]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG c d).intervalIntegrable a b)

lemma boxIntegral_sub (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry) :
    boxIntegral a b c d (fun x y => F x y - G x y) =
      boxIntegral a b c d F - boxIntegral a b c d G := by
  unfold boxIntegral
  simp_rw [intervalIntegral.integral_sub
    ((hF.uncurry_left _).intervalIntegrable c d) ((hG.uncurry_left _).intervalIntegrable c d)]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG c d).intervalIntegrable a b)

lemma boxIntegral_const_mul (a b c d t : ℝ) (F : ℝ → ℝ → ℝ) :
    boxIntegral a b c d (fun x y => t * F x y) = t * boxIntegral a b c d F := by
  simp only [boxIntegral, intervalIntegral.integral_const_mul]

lemma boxIntegral_swap (a b c d : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) :
    boxIntegral a b c d F = boxIntegral c d a b (fun y x => F x y) := by
  apply intervalIntegral_intervalIntegral_swap
  exact (ContinuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc) hF.continuousOn).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

lemma boxIntegral_nonneg {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℝ} (hF : ∀ x y, 0 ≤ F x y) : 0 ≤ boxIntegral a b c d F := by
  apply intervalIntegral.integral_nonneg hab
  intro x _
  exact intervalIntegral.integral_nonneg hcd (fun y _ => hF x y)

lemma endpoint_defect {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b y : ℝ) :
    (∫ x in a..b, k (x-y)) - (b-a) * ((k (a-y) + k (b-y))/2) =
      -(∫ x in a..b, (x-(a+b)/2) * k' (x-y)) := by
  have hkxy : Continuous (fun x : ℝ => k (x-y)) := hk.comp (continuous_id.sub continuous_const)
  have hk'xy : Continuous (fun x : ℝ => k' (x-y)) := hk'.comp (continuous_id.sub continuous_const)
  have hdkxy (x : ℝ) : HasDerivAt (fun x : ℝ => k (x-y)) (k' (x-y)) x := by
    convert (hderiv (x-y)).comp x ((hasDerivAt_id x).sub_const y) using 1 <;>
      first | rfl | simp only [mul_one]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x-(a+b)/2) (v := fun x : ℝ => k (x-y))
    (u' := fun _ => 1) (v' := fun x => k' (x-y))
    (continuous_id.sub continuous_const).continuousOn hkxy.continuousOn
    (fun x _ => (hasDerivAt_id x).sub_const ((a+b)/2)) (fun x _ => hdkxy x)
    (continuous_const.intervalIntegrable a b) (hk'xy.intervalIntegrable a b)
  simp only [one_mul] at hparts
  linarith [hparts]

lemma endpoint_defect_right {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (c d x : ℝ) :
    (∫ y in c..d, k (x-y)) - (d-c) * ((k (x-c) + k (x-d))/2) =
      ∫ y in c..d, (y-(c+d)/2) * k' (x-y) := by
  have hkxy : Continuous (fun y : ℝ => k (x-y)) := hk.comp (continuous_const.sub continuous_id)
  have hk'xy : Continuous (fun y : ℝ => -k' (x-y)) := (hk'.comp (continuous_const.sub continuous_id)).neg
  have hdkxy (y : ℝ) : HasDerivAt (fun y : ℝ => k (x-y)) (-k' (x-y)) y := by
    convert (hderiv (x-y)).comp y ((hasDerivAt_id y).const_sub x) using 1 <;>
      first | rfl | simp only [mul_neg, mul_one]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => y-(c+d)/2) (v := fun y : ℝ => k (x-y))
    (u' := fun _ => 1) (v' := fun y => -k' (x-y))
    (continuous_id.sub continuous_const).continuousOn hkxy.continuousOn
    (fun y _ => (hasDerivAt_id y).sub_const ((c+d)/2)) (fun y _ => hdkxy y)
    (continuous_const.intervalIntegrable c d) (hk'xy.intervalIntegrable c d)
  simp only [one_mul, mul_neg, intervalIntegral.integral_neg] at hparts
  linarith [hparts]

lemma box_endpoint_defect_left {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k (x-y) - (k (a-y)+k (b-y))/2) =
      boxIntegral a b c d (fun x y => -((x-(a+b)/2)*k' (x-y))) := by
  rw [boxIntegral_swap a b c d (by fun_prop),
    boxIntegral_swap a b c d (by fun_prop)]
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  have hkxy : Continuous (fun x : ℝ => k (x-y)) := hk.comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_sub (g := fun _ : ℝ => (k (a-y)+k (b-y))/2) (hkxy.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const,
    intervalIntegral.integral_neg, smul_eq_mul]
  exact endpoint_defect hk hk' hderiv a b y

lemma box_endpoint_defect_right {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k (x-y) - (k (x-c)+k (x-d))/2) =
      boxIntegral a b c d (fun x y => (y-(c+d)/2)*k' (x-y)) := by
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  have hkxy : Continuous (fun y : ℝ => k (x-y)) := hk.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_sub (g := fun _ : ℝ => (k (x-c)+k (x-d))/2) (hkxy.intervalIntegrable c d)
    (continuous_const.intervalIntegrable c d), intervalIntegral.integral_const, smul_eq_mul]
  exact endpoint_defect_right hk hk' hderiv c d x

lemma box_midpoint_identity {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => 2*k (x-y) - (k (a-y)+k (b-y))/2 -
      (k (x-c)+k (x-d))/2) =
    boxIntegral a b c d (fun x y => -(x-y-((a+b)/2-(c+d)/2))*k' (x-y)) := by
  calc
    _ = boxIntegral a b c d (fun x y =>
        (k (x-y) - (k (a-y)+k (b-y))/2) + (k (x-y) - (k (x-c)+k (x-d))/2)) := by
          apply boxIntegral_congr; intros; ring
    _ = boxIntegral a b c d (fun x y => k (x-y) - (k (a-y)+k (b-y))/2) +
        boxIntegral a b c d (fun x y => k (x-y) - (k (x-c)+k (x-d))/2) :=
          boxIntegral_add a b c d (by fun_prop) (by fun_prop)
    _ = boxIntegral a b c d (fun x y => -((x-(a+b)/2)*k' (x-y))) +
        boxIntegral a b c d (fun x y => (y-(c+d)/2)*k' (x-y)) := by
          rw [box_endpoint_defect_left hk hk' hderiv, box_endpoint_defect_right hk hk' hderiv]
    _ = boxIntegral a b c d (fun x y =>
        -((x-(a+b)/2)*k' (x-y)) + (y-(c+d)/2)*k' (x-y)) :=
          (boxIntegral_add a b c d (by fun_prop) (by fun_prop)).symm
    _ = _ := by apply boxIntegral_congr; intros; ring


lemma box_integral_derivative {k k' : ℝ → ℝ} (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k' (x-y)) =
      ∫ y in c..d, (k (b-y)-k (a-y)) := by
  rw [boxIntegral_swap a b c d (by fun_prop)]
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    convert (hderiv (x-y)).comp x ((hasDerivAt_id x).sub_const y) using 1 <;>
      first | rfl | simp only [mul_one]
  · exact (hk'.comp (continuous_id.sub continuous_const)).intervalIntegrable a b

lemma box_midpoint_sign {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((a+b)/2-(c+d)/2) * boxIntegral a b c d (fun x y => k' (x-y)) ≤ 0 := by
  rw [box_integral_derivative hk' hderiv]
  exact midpoint_endpoint_sign hk heven hanti hab hcd

/-- General interval comparison before substituting the Newton kernel. -/
lemma box_endpoint_comparison {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    boxIntegral a b c d (fun x y => 2*k (x-y) - (k (a-y)+k (b-y))/2 -
      (k (x-c)+k (x-d))/2) ≤
      boxIntegral a b c d (fun x y => -(x-y)*k' (x-y)) := by
  rw [box_midpoint_identity hk hk' hderiv]
  have hsplit : boxIntegral a b c d
      (fun x y => -(x-y-((a+b)/2-(c+d)/2))*k' (x-y)) =
      boxIntegral a b c d (fun x y => -(x-y)*k' (x-y)) +
      ((a+b)/2-(c+d)/2) * boxIntegral a b c d (fun x y => k' (x-y)) := by
    calc
      _ = boxIntegral a b c d (fun x y => -(x-y)*k' (x-y) +
          ((a+b)/2-(c+d)/2)*k' (x-y)) := by
            apply boxIntegral_congr; intros; ring
      _ = _ := by
        rw [boxIntegral_add a b c d (by fun_prop) (by fun_prop), boxIntegral_const_mul]
  rw [hsplit]
  linarith [box_midpoint_sign hk hk' hderiv heven hanti hab hcd]

lemma kernel_derivative_continuous (n : ℕ) {l : ℝ} (hl : 0 < l) (c : ℝ) :
    Continuous (fun h : ℝ => -((n : ℝ)-2)*h/(l^2+h^2)*kernel n l c h) := by
  apply Continuous.mul _ (kernel_continuous n hl c)
  exact (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun x => ne_of_gt (base_pos hl x))

/-- The two unweighted endpoint defects are controlled by the directional interaction. -/
lemma newton_endpoint_comparison (n : ℕ) (hn : 3 ≤ n) {l C a b c d : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hab : a ≤ b) (hcd : c ≤ d) :
    boxIntegral a b c d (fun x y => 2*kernel n l C (x-y) -
      (kernel n l C (a-y)+kernel n l C (b-y))/2 -
      (kernel n l C (x-c)+kernel n l C (x-d))/2) ≤
      ((n : ℝ)-2)*boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) := by
  have h := box_endpoint_comparison (kernel_continuous n hl C)
    (kernel_derivative_continuous n hl C) (kernel_hasDerivAt n hl C)
    (kernel_even n l C) (fun hxy => kernel_antitone_abs n hn hl hC hxy) hab hcd
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [← boxIntegral_const_mul]
      apply boxIntegral_congr
      intro x y
      ring

lemma weighted_scalar_comparison {K EI EJ T cI cJ : ℝ}
    (hEI : 0 ≤ EI) (hEJ : 0 ≤ EJ) (hI : 0 ≤ cI) (hJ : 0 ≤ cJ)
    (hpair : 2*K-EI-EJ ≤ T) :
    (cI+cJ)*K ≤ cI*EI+cJ*EJ+min cI cJ*T+|cI-cJ| * K := by
  rcases le_total cI cJ with hij | hji
  · rw [min_eq_left hij, abs_of_nonpos (sub_nonpos.mpr hij)]
    have h := mul_le_mul_of_nonneg_left hpair hI
    have h' := mul_nonneg (sub_nonneg.mpr hij) hEJ
    nlinarith
  · rw [min_eq_right hji, abs_of_nonneg (sub_nonneg.mpr hji)]
    have h := mul_le_mul_of_nonneg_left hpair hJ
    have h' := mul_nonneg (sub_nonneg.mpr hji) hEI
    nlinarith

/-- Weighted interval comparison, with finite endpoints.  The normalizing
constant `C` may be instantiated by `1 / ((n-2) * area(S^(n-1)))`. -/
lemma bounded_weighted_interval_comparison (n : ℕ) (hn : 3 ≤ n)
    {l C a b c d cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hab : a ≤ b) (hcd : c ≤ d) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) :
    (cI+cJ) * boxIntegral a b c d (fun x y => kernel n l C (x-y)) ≤
      cI * boxIntegral a b c d (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ * boxIntegral a b c d (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n : ℝ)-2)*min cI cJ) * boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) +
      |cI-cJ| * boxIntegral a b c d (fun x y => kernel n l C (x-y)) := by
  have hk := kernel_continuous n hl C
  have hcomp := newton_endpoint_comparison n hn hl hC hab hcd
  rw [boxIntegral_sub a b c d (by fun_prop) (by fun_prop),
      boxIntegral_sub a b c d (by fun_prop) (by fun_prop), boxIntegral_const_mul] at hcomp
  have hEI : 0 ≤ boxIntegral a b c d
      (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) := by
    apply boxIntegral_nonneg hab hcd
    intro x y
    exact div_nonneg (add_nonneg (kernel_nonneg n hC (a-y)) (kernel_nonneg n hC (b-y))) (by norm_num)
  have hEJ : 0 ≤ boxIntegral a b c d
      (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) := by
    apply boxIntegral_nonneg hab hcd
    intro x y
    exact div_nonneg (add_nonneg (kernel_nonneg n hC (x-c)) (kernel_nonneg n hC (x-d))) (by norm_num)
  have hw := weighted_scalar_comparison hEI hEJ hcI hcJ hcomp
  nlinarith [hw]


lemma ofReal_boxIntegral {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℝ} (hF : Continuous F.uncurry) (hpos : ∀ x y, 0 ≤ F x y) :
    ENNReal.ofReal (boxIntegral a b c d F) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, ENNReal.ofReal (F x y) := by
  simp only [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  unfold boxIntegral
  rw [intervalIntegral.integral_of_le hab]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · apply lintegral_congr
    intro x
    rw [intervalIntegral.integral_of_le hcd]
    exact ofReal_integral_eq_lintegral_ofReal
      (by
        change IntegrableOn (F x) (Ioc c d) volume
        exact ((hF.uncurry_left x).intervalIntegrable c d).1)
      (Filter.Eventually.of_forall (hpos x))
  · change IntegrableOn _ (Ioc a b) volume
    exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b).1
  · exact Filter.Eventually.of_forall fun x =>
      intervalIntegral.integral_nonneg hcd (fun y _ => hpos x y)

lemma bounded_weighted_interval_lintegral (n : ℕ) (hn : 3 ≤ n)
    {l C a b c d cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hab : a ≤ b) (hcd : c ≤ d) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
      ENNReal.ofReal ((cI+cJ)*kernel n l C (x-y))) ≤
    ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
      ENNReal.ofReal (cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
        cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
        (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y)) := by
  have hk := kernel_continuous n hl C
  have hD : Continuous (fun z : ℝ × ℝ => (z.1-z.2)^2/(l^2+(z.1-z.2)^2)) :=
    ((continuous_fst.sub continuous_snd).pow 2).div
      (continuous_const.add ((continuous_fst.sub continuous_snd).pow 2))
      (fun z => ne_of_gt (base_pos hl (z.1-z.2)))
  have hpc (x y : ℝ) : 0 ≤ (x-y)^2/(l^2+(x-y)^2) :=
    div_nonneg (sq_nonneg _) (base_pos hl _).le
  have hn' : 0 ≤ (n : ℝ)-2 := by exact_mod_cast (show 0 ≤ (n : ℤ)-2 by omega)
  have hleft : ∀ x y, 0 ≤ (cI+cJ)*kernel n l C (x-y) :=
    fun x y => mul_nonneg (add_nonneg hcI hcJ) (kernel_nonneg n hC _)
  have hright (x y : ℝ) : 0 ≤ cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
        cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
        (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y) := by
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg hcI (div_nonneg
          (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num))
      · exact mul_nonneg hcJ (div_nonneg
          (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num))
    · exact mul_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hn' (le_min hcI hcJ)) (hpc x y)) (abs_nonneg _))
        (kernel_nonneg n hC _)
  rw [← ofReal_boxIntegral hab hcd (by fun_prop (disch := positivity)) hleft,
      ← ofReal_boxIntegral hab hcd (by fun_prop (disch := positivity)) hright]
  apply ENNReal.ofReal_le_ofReal
  have heq : boxIntegral a b c d (fun x y =>
      cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y)) =
      cI * boxIntegral a b c d (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ * boxIntegral a b c d (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n:ℝ)-2)*min cI cJ) * boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) +
      |cI-cJ| * boxIntegral a b c d (fun x y => kernel n l C (x-y)) := by
    calc
      _ = boxIntegral a b c d (fun x y =>
          (cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
           cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
           (((n:ℝ)-2)*min cI cJ)*((x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y))) +
           |cI-cJ| *kernel n l C (x-y)) := by
        apply boxIntegral_congr; intros; ring
      _ = _ := by
        rw [boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity)),
          boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity)),
          boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity))]
        simp only [boxIntegral_const_mul]
  rw [heq, boxIntegral_const_mul]
  exact bounded_weighted_interval_comparison n hn hl hC hab hcd hcI hcJ

/-- The four kinds of nonempty open real intervals. `Valid` excludes reversed
finite endpoints; no endpoints at infinity are ever evaluated. -/
inductive OpenInterval where
  | bounded (a b : ℝ)
  | below (b : ℝ)
  | above (a : ℝ)
  | all

namespace OpenInterval

def carrier : OpenInterval → Set ℝ
  | .bounded a b => Ioo a b
  | .below b => Iio b
  | .above a => Ioi a
  | .all => univ

def Valid : OpenInterval → Prop
  | .bounded a b => a < b
  | _ => True

def IsBounded : OpenInterval → Prop
  | .bounded _ _ => True
  | _ => False

noncomputable def leftAverage (I : OpenInterval) (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  match I with
  | .bounded a b => (k (a-y)+k (b-y))/2
  | _ => 0

noncomputable def rightAverage (J : OpenInterval) (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  match J with
  | .bounded c d => (k (x-c)+k (x-d))/2
  | _ => 0

lemma leftAverage_nonneg (I : OpenInterval) {k : ℝ → ℝ} (hk : ∀ x, 0 ≤ k x) (y : ℝ) :
    0 ≤ I.leftAverage k y := by
  cases I <;> simp only [leftAverage]
  · exact div_nonneg (add_nonneg (hk _) (hk _)) (by norm_num)
  all_goals exact le_rfl

lemma rightAverage_nonneg (I : OpenInterval) {k : ℝ → ℝ} (hk : ∀ x, 0 ≤ k x) (y : ℝ) :
    0 ≤ I.rightAverage k y := by
  cases I <;> simp only [rightAverage]
  · exact div_nonneg (add_nonneg (hk _) (hk _)) (by norm_num)
  all_goals exact le_rfl

lemma exists_bounded (I : OpenInterval) (h : I.IsBounded) : ∃ a b, I = .bounded a b := by
  cases I <;> simp_all [IsBounded]

end OpenInterval

/-- The full interval comparison, including unbounded zero-weight intervals.
All expressions are nonnegative extended integrals, so no divergent quantities
are subtracted. The harmless zero continuation of the endpoint average is
used only when the corresponding coefficient vanishes. -/
lemma weighted_interval_comparison (n : ℕ) (hn : 3 ≤ n)
    (I J : OpenInterval) (hI : I.Valid) (hJ : J.Valid)
    {l C cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ)
    (hboundedI : 0 < cI → I.IsBounded) (hboundedJ : 0 < cJ → J.IsBounded) :
    (∫⁻ x in I.carrier, ∫⁻ y in J.carrier,
      ENNReal.ofReal ((cI+cJ)*kernel n l C (x-y))) ≤
    ∫⁻ x in I.carrier, ∫⁻ y in J.carrier,
      ENNReal.ofReal (cI*I.leftAverage (kernel n l C) y +
        cJ*J.rightAverage (kernel n l C) x +
        (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y)) := by
  by_cases hzI : cI = 0
  · subst cI
    apply lintegral_mono; intro x
    apply lintegral_mono; intro y
    apply ENNReal.ofReal_le_ofReal
    simp only [zero_add, zero_mul, min_eq_left hcJ, mul_zero, zero_sub, abs_neg, abs_of_nonneg hcJ]
    exact le_add_of_nonneg_left (mul_nonneg hcJ (J.rightAverage_nonneg (kernel_nonneg n hC) x))
  by_cases hzJ : cJ = 0
  · subst cJ
    apply lintegral_mono; intro x
    apply lintegral_mono; intro y
    apply ENNReal.ofReal_le_ofReal
    simp only [add_zero, zero_mul, min_eq_right hcI, mul_zero, zero_add, sub_zero, abs_of_nonneg hcI]
    exact le_add_of_nonneg_left (mul_nonneg hcI (I.leftAverage_nonneg (kernel_nonneg n hC) y))
  obtain ⟨a,b,rfl⟩ := I.exists_bounded (hboundedI (lt_of_le_of_ne hcI (Ne.symm hzI)))
  obtain ⟨c,d,rfl⟩ := J.exists_bounded (hboundedJ (lt_of_le_of_ne hcJ (Ne.symm hzJ)))
  exact bounded_weighted_interval_lintegral n hn hl hC hI.le hJ.le hcI hcJ

end HenonLaneEmden.IntervalGeometry
end Intervals

end OAI
