import OAI.Geometry.RCD.Metric.MetricLimit
import OAI.Analysis.RCDHeat.Foundations
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Abel

namespace OAI

/-!
# Constructive openness of approximate Euclidean coordinates

The hypotheses below are the scale-dependent approximation and nearby-metric
estimates used in `co:open-coordinates`.  Exact preimages and openness are proved
by a convergent correction process; neither is an input.
-/

open Filter Set
open scoped Topology

namespace RegularPointCoordinates

section Correction

variable {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y]

/-- A quarter-scale correction process stays strictly inside the working ball
and converges to an exact preimage.  The predicate records the current residual
in a possibly changing norm. -/
theorem exists_preimage_of_quarter_corrections
    {f : X → Y} {x₀ : X} {P : Y} {r M : ℝ} (hr : 0 < r)
    (control : ℕ → X → Prop) (hzero : control 0 x₀)
    (hstep : ∀ n x, dist x x₀ < r / 2 → control n x →
      ∃ y, dist y x ≤ r * (1 / 4 : ℝ) ^ n / 8 ∧ control (n + 1) y)
    (hresidual : ∀ n x, dist x x₀ < r / 2 → control n x →
      dist (f x) P ≤ M * (r * (1 / 4 : ℝ) ^ n))
    (hcont : ContinuousOn f (Metric.ball x₀ (r / 2))) :
    ∃ y, dist y x₀ ≤ r / 6 ∧ f y = P := by
  classical
  let next (n : ℕ) (x : X) : X :=
    if h : dist x x₀ < r / 2 ∧ control n x then
      Classical.choose (hstep n x h.1 h.2) else x
  let a : ℕ → X := fun n => Nat.rec x₀ next n
  have ha0 : a 0 = x₀ := rfl
  have hasucc (n : ℕ) : a (n + 1) = next n (a n) := rfl
  have hinv : ∀ n, dist (a n) x₀ ≤ r / 6 * (1 - (1 / 4 : ℝ) ^ n) ∧
      control n (a n) := by
    intro n
    induction n with
    | zero => simpa only [ha0, pow_zero, sub_self, mul_zero, dist_self] using
        And.intro (le_refl (0 : ℝ)) hzero
    | succ n ih =>
      have hpow : 0 ≤ (1 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
      have hin : dist (a n) x₀ < r / 2 := by nlinarith [ih.1]
      have hn := Classical.choose_spec (hstep n (a n) hin ih.2)
      have hnext : a (n + 1) = Classical.choose (hstep n (a n) hin ih.2) := by
        simp [hasucc, next, hin, ih.2]
      rw [hnext]
      refine ⟨?_, hn.2⟩
      have ht := dist_triangle (Classical.choose (hstep n (a n) hin ih.2)) (a n) x₀
      rw [pow_succ]
      nlinarith [hn.1, ih.1]
  have hin (n : ℕ) : dist (a n) x₀ < r / 2 := by
    have hp : 0 ≤ (1 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
    nlinarith [(hinv n).1]
  have hdist (n : ℕ) : dist (a n) (a (n + 1)) ≤ (r / 8) * (1 / 4 : ℝ) ^ n := by
    have hn := Classical.choose_spec (hstep n (a n) (hin n) (hinv n).2)
    have hnxt : a (n + 1) = Classical.choose (hstep n (a n) (hin n) (hinv n).2) := by
      simp [hasucc, next, hin n, (hinv n).2]
    rw [dist_comm, hnxt]
    nlinarith [hn.1]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 4 : ℝ) (r / 8) (by norm_num) hdist)
  have hybound : dist y x₀ ≤ r / 6 := by
    have hb := dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) (r / 8)
      (by norm_num) hdist hy 0
    rw [dist_comm]
    calc
      dist x₀ y ≤ (r / 8) / (1 - 1 / 4 : ℝ) := by
        simpa only [ha0, pow_zero, mul_one] using hb
      _ = r / 6 := by ring
  have hymem : y ∈ Metric.ball x₀ (r / 2) := by
    exact lt_of_le_of_lt hybound (by linarith)
  have hf : Tendsto (fun n => f (a n)) atTop (𝓝 (f y)) :=
    (hcont.continuousAt (Metric.isOpen_ball.mem_nhds hymem)).tendsto.comp hy
  have hp : Tendsto (fun n => dist (f (a n)) P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => dist_nonneg) (fun n => hresidual n (a n) (hin n) (hinv n).2)
    simpa only [mul_zero] using (tendsto_const_nhds (x := M)).mul
      ((tendsto_const_nhds (x := r)).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)))
  have heq : dist (f y) P = 0 := tendsto_nhds_unique (hf.dist tendsto_const_nhds) hp
  exact ⟨y, hybound, dist_eq_zero.mp heq⟩

end Correction

section Normalized

variable {X E : Type*} [MetricSpace X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [CompleteSpace X] in
/-- Pointed metric approximation and uniform closeness of the normalized
coordinate map supply the Euclidean correspondence needed below. -/
theorem euclidean_correspondence_of_pointed_approximation
    {f g : X → E} {x : X} {r : ℝ} (hr : 0 < r) (N : E ≃L[ℝ] E)
    (hg : IsPointedApproximation x 0 r 1 (1 / 1024) g)
    (hclose : ∀ y, dist y x ≤ r →
      ‖r⁻¹ • N (f y - f x) - g y‖ ≤ 1 / 1024) :
    ∀ a : E, ‖a‖ < r / 16 →
      ∃ y, dist y x ≤ ‖a‖ + r / 256 ∧ ‖N (f y - f x) - a‖ ≤ r / 256 := by
  intro a ha
  have hscale (b : E) : ‖r⁻¹ • b‖ = ‖b‖ / r := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_eq_inv_mul]
  have hat : ‖r⁻¹ • a‖ < 1 / 16 := by
    rw [hscale, div_lt_iff₀ hr]
    linarith
  obtain ⟨y, hy, hgy⟩ := hg.2.2 (r⁻¹ • a) (by
    rw [dist_zero_right]
    linarith)
  have hy' : dist y x ≤ r := by simpa only [one_mul] using hy
  have hmetric := hg.2.1 y x hy (by simp only [dist_self, one_mul]; positivity)
  have hbase := hg.1
  have htri := dist_triangle4 (g y) (r⁻¹ • a) 0 (g x)
  rw [dist_zero_right, dist_zero_left, ← dist_zero_right (g x)] at htri
  have hdist : dist y x / r ≤ ‖a‖ / r + 3 / 1024 := by
    rw [hscale] at htri
    linarith [(abs_le.mp hmetric).1]
  have hdist' := mul_le_mul_of_nonneg_right hdist hr.le
  rw [add_mul, div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne'] at hdist'
  have hres : ‖r⁻¹ • (N (f y - f x) - a)‖ ≤ 2 / 1024 := by
    rw [smul_sub]
    have ht := dist_triangle (r⁻¹ • N (f y - f x)) (g y) (r⁻¹ • a)
    simp only [dist_eq_norm] at ht hgy
    linarith [hclose y hy']
  rw [hscale] at hres
  have hres' := (div_le_iff₀ hr).mp hres
  exact ⟨y, by linarith, by linarith⟩

omit [CompleteSpace X] in
/-- The approximate correction hypothesis follows directly from a normalized
Euclidean correspondence: test the correspondence at the normalized target.
The displacement error and coordinate error are both explicit. -/
theorem approximate_preimage_of_euclidean_correspondence
    {f : X → E} {x : X} {R : ℝ} (N : E ≃L[ℝ] E)
    (hcorrespondence : ∀ a : E, ‖a‖ < R / 16 →
      ∃ y, dist y x ≤ ‖a‖ + R / 256 ∧ ‖N (f y - f x) - a‖ ≤ R / 256)
    {P : E} (hP : ‖N (P - f x)‖ < R / 16) :
    ∃ y, dist y x ≤ 17 / 256 * R ∧ ‖N (P - f y)‖ ≤ R / 256 := by
  obtain ⟨y, hy, herr⟩ := hcorrespondence (N (P - f x)) hP
  refine ⟨y, by linarith, ?_⟩
  have hid : N (f y - f x) - N (P - f x) = -(N (P - f y)) := by
    simp only [map_sub, neg_sub]
    abel
  simpa only [hid, norm_neg] using herr

/-- Concrete constants for the correction argument.  `N n x` represents the
inverse square root of the Gram matrix at the current scale and center. -/
theorem exists_preimage_of_normalized_approximation
    {f : X → E} {x₀ : X} {P : E} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (N : ℕ → X → E ≃L[ℝ] E)
    (hzero : ‖N 0 x₀ (P - f x₀)‖ < r / 16)
    (happrox : ∀ n x, dist x x₀ < r / 2 →
      ‖N n x (P - f x)‖ < r * (1 / 4 : ℝ) ^ n / 16 →
      ∃ y, dist y x ≤ 17 / 256 * (r * (1 / 4 : ℝ) ^ n) ∧
        ‖N n x (P - f y)‖ ≤ r * (1 / 4 : ℝ) ^ n / 256)
    (hnear : ∀ n x y, dist x x₀ < r / 2 → dist y x ≤ r * (1 / 4 : ℝ) ^ n / 8 →
      ∀ w, ‖N (n + 1) y w‖ ≤ 2 * ‖N n x w‖)
    (hupper : ∀ n x, dist x x₀ < r / 2 → ∀ w, ‖w‖ ≤ C * ‖N n x w‖)
    (hcont : ContinuousOn f (Metric.ball x₀ (r / 2))) :
    ∃ y, dist y x₀ ≤ r / 6 ∧ f y = P := by
  let control : ℕ → X → Prop := fun n x =>
    ‖N n x (P - f x)‖ < r * (1 / 4 : ℝ) ^ n / 16
  apply exists_preimage_of_quarter_corrections hr control (by simpa [control] using hzero)
    (M := C / 16) ?_ ?_ hcont
  · intro n x hx hc
    obtain ⟨y, hxy, hy⟩ := happrox n x hx hc
    have hrn : 0 < r * (1 / 4 : ℝ) ^ n := mul_pos hr (pow_pos (by norm_num) n)
    have hxy' : dist y x ≤ r * (1 / 4 : ℝ) ^ n / 8 := by nlinarith
    refine ⟨y, hxy', ?_⟩
    dsimp [control]
    have hn := hnear n x y hx hxy' (P - f y)
    rw [pow_succ]
    nlinarith
  · intro n x hx hc
    have hu := hupper n x hx (P - f x)
    have hm := mul_le_mul_of_nonneg_left hc.le hC
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith

end Normalized

section OpenImage

variable {X E : Type*} [MetricSpace X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quarter scales used in the constructive surjectivity argument. -/
noncomputable def coordinateQuarterRadius (r : ℝ) (i : ℕ) : ℝ := r * (1 / 4 : ℝ) ^ i

theorem coordinateQuarterRadius_add (r : ℝ) (i n : ℕ) :
    coordinateQuarterRadius r (i + n) =
      coordinateQuarterRadius r i * (1 / 4 : ℝ) ^ n := by
  simp only [coordinateQuarterRadius, pow_add, mul_assoc]

/-- Raw approximation data: small normalized targets have approximate
preimages, and changing the center and going down one quarter-scale costs at
most two in the residual norm.  All conditions are local to the open domain. -/
structure OpenCoordinateData (Ω : Set X) (f : X → E) (r C : ℝ) where
  normalization : ℕ → X → E ≃L[ℝ] E
  approximate : ∀ i x, x ∈ Ω → Metric.closedBall x (coordinateQuarterRadius r i) ⊆ Ω →
    ∀ P, ‖normalization i x (P - f x)‖ < coordinateQuarterRadius r i / 16 →
    ∃ y, dist y x ≤ 17 / 256 * coordinateQuarterRadius r i ∧
      ‖normalization i x (P - f y)‖ ≤ coordinateQuarterRadius r i / 256
  nearby : ∀ i x y, x ∈ Ω → y ∈ Ω →
    dist y x ≤ coordinateQuarterRadius r i / 8 →
    ∀ w, ‖normalization (i + 1) y w‖ ≤ 2 * ‖normalization i x w‖
  upper : ∀ i x, x ∈ Ω → ∀ w, ‖w‖ ≤ C * ‖normalization i x w‖

namespace OpenCoordinateData

/-- Build the approximation data directly from pointed metric approximations
and uniform closeness of the normalized coordinate functions. -/
def of_pointed_approximation {Ω : Set X} {f : X → E} {r C : ℝ} (hr : 0 < r)
    (N : ℕ → X → E ≃L[ℝ] E)
    (hcharts : ∀ i x, x ∈ Ω → Metric.closedBall x (coordinateQuarterRadius r i) ⊆ Ω →
      ∃ g : X → E,
        IsPointedApproximation x 0 (coordinateQuarterRadius r i) 1 (1 / 1024) g ∧
        ∀ y, dist y x ≤ coordinateQuarterRadius r i →
          ‖(coordinateQuarterRadius r i)⁻¹ • N i x (f y - f x) - g y‖ ≤ 1 / 1024)
    (hnear : ∀ i x y, x ∈ Ω → y ∈ Ω →
      dist y x ≤ coordinateQuarterRadius r i / 8 →
      ∀ w, ‖N (i + 1) y w‖ ≤ 2 * ‖N i x w‖)
    (hupper : ∀ i x, x ∈ Ω → ∀ w, ‖w‖ ≤ C * ‖N i x w‖) :
    OpenCoordinateData Ω f r C where
  normalization := N
  approximate := by
    intro i x hx hb P hP
    obtain ⟨g, hg, hclose⟩ := hcharts i x hx hb
    exact approximate_preimage_of_euclidean_correspondence (N i x)
      (euclidean_correspondence_of_pointed_approximation
        (mul_pos hr (pow_pos (by norm_num) i)) (N i x) hg hclose) hP
  nearby := hnear
  upper := hupper

/-- An exact ellipsoid is contained in the image of the interior ball.  The
stronger one-sixth radius records the margin left by the Cauchy construction. -/
theorem exists_preimage {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hcont : ContinuousOn f Ω) (i : ℕ) (x₀ : X)
    (hball : Metric.ball x₀ (2 * coordinateQuarterRadius r i) ⊆ Ω)
    {P : E} (hP : ‖d.normalization i x₀ (P - f x₀)‖ <
      coordinateQuarterRadius r i / 16) :
    ∃ y, dist y x₀ ≤ coordinateQuarterRadius r i / 6 ∧ f y = P := by
  let R := coordinateQuarterRadius r i
  have hR : 0 < R := mul_pos hr (pow_pos (by norm_num) i)
  have hscale (n : ℕ) : coordinateQuarterRadius r (i + n) = R * (1 / 4 : ℝ) ^ n :=
    coordinateQuarterRadius_add r i n
  have hle (n : ℕ) : coordinateQuarterRadius r (i + n) ≤ R := by
    rw [hscale]
    exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hinside {x : X} (hx : dist x x₀ < R / 2) : x ∈ Ω :=
    hball (by change dist x x₀ < 2 * R; linarith)
  apply exists_preimage_of_normalized_approximation hR hC
    (fun n x => d.normalization (i + n) x) (by simpa using hP) ?_ ?_ ?_ ?_
  · intro n x hx ht
    have hb : Metric.closedBall x (coordinateQuarterRadius r (i + n)) ⊆ Ω := by
      intro z hz
      apply hball
      have htri := dist_triangle z x x₀
      change dist z x₀ < 2 * R
      have hz' : dist z x ≤ coordinateQuarterRadius r (i + n) := hz
      linarith [hle n]
    simpa only [hscale] using d.approximate (i + n) x (hinside hx) hb P
      (by simpa only [hscale] using ht)
  · intro n x y hx hxy w
    have hy : y ∈ Ω := by
      apply hball
      have htri := dist_triangle y x x₀
      have hxy' : dist y x ≤ coordinateQuarterRadius r (i + n) / 8 := by
        simpa only [hscale] using hxy
      change dist y x₀ < 2 * R
      linarith [hle n]
    simpa only [Nat.add_assoc] using d.nearby (i + n) x y (hinside hx) hy
      (by simpa only [hscale] using hxy) w
  · intro n x hx w
    exact d.upper (i + n) x (hinside hx) w
  · exact hcont.mono (fun x hx => hinside hx)

/-- Approximation on all quarter-scales gives arbitrarily localized exact
preimages.  The target neighborhood is an explicit frozen ellipsoid. -/
theorem localized_surjectivity {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) {x : X} (hx : x ∈ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, ∀ P, ‖d.normalization i x (P - f x)‖ < coordinateQuarterRadius r i / 16 →
      ∃ y ∈ Ω, dist y x < δ ∧ f y = P := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hlim : Tendsto (fun i => coordinateQuarterRadius r i) atTop (𝓝 0) := by
    simpa only [coordinateQuarterRadius, mul_zero] using (tendsto_const_nhds (x := r)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1))
  have hev : ∀ᶠ i in atTop, coordinateQuarterRadius r i < min (a / 2) δ :=
    hlim.eventually (gt_mem_nhds (by positivity : 0 < min (a / 2) δ))
  obtain ⟨i, hi⟩ := hev.exists
  have hR : 0 < coordinateQuarterRadius r i := mul_pos hr (pow_pos (by norm_num) i)
  refine ⟨i, fun P hP => ?_⟩
  have hb : Metric.ball x (2 * coordinateQuarterRadius r i) ⊆ Ω := by
    intro y hy
    apply hball
    have hy' : dist y x < 2 * coordinateQuarterRadius r i := hy
    change dist y x < a
    linarith [lt_of_lt_of_le hi (min_le_left _ _)]
  obtain ⟨y, hy, hfy⟩ := d.exists_preimage hr hC hcont i x hb hP
  refine ⟨y, hb ?_, ?_, hfy⟩
  · change dist y x < 2 * coordinateQuarterRadius r i
    linarith
  · linarith [lt_of_lt_of_le hi (min_le_right _ _)]

/-- The restriction of the coordinates to the open working domain is an open
map.  This uses exact preimages, without any invariance-of-domain input. -/
theorem isOpenMap {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) :
    IsOpenMap (fun x : Ω => f x) := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro P ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨i, hi⟩ := d.localized_surjectivity hr hC hΩ hcont x.property hδ
  let V := {P : E | ‖d.normalization i x (P - f x)‖ < coordinateQuarterRadius r i / 16}
  have hVopen : IsOpen V := isOpen_lt
    ((d.normalization i x).continuous.comp (continuous_id.sub continuous_const)).norm
    continuous_const
  have hxV : f x ∈ V := by
    change ‖d.normalization i x (f x - f x)‖ < coordinateQuarterRadius r i / 16
    simp only [sub_self, map_zero, norm_zero]
    exact div_pos (mul_pos hr (pow_pos (by norm_num) i)) (by norm_num)
  apply Filter.mem_of_superset (hVopen.mem_nhds hxV)
  intro P hP
  obtain ⟨y, hy, hdist, hfy⟩ := hi P hP
  exact ⟨⟨y, hy⟩, hδU hdist, hfy⟩

/-- Once separation has been proved, the constructive open map is an open
embedding, hence a homeomorphism onto its open image. -/
theorem isOpenEmbedding {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) (hinj : Set.InjOn f Ω) :
    Topology.IsOpenEmbedding (fun x : Ω => f x) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuousOn_iff_continuous_domRestrict.mp hcont
  · intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  · exact d.isOpenMap hr hC hΩ hcont

/-- The resulting homeomorphism retains the original coordinate values. -/
noncomputable def homeomorph {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) (hinj : Set.InjOn f Ω) :
    Ω ≃ₜ Set.range (fun x : Ω => f x) :=
  (d.isOpenEmbedding hr hC hΩ hcont hinj).toIsEmbedding.toHomeomorph

theorem isOpen_range {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) :
    IsOpen (Set.range (fun x : Ω => f x)) := by
  simpa only [Set.image_univ] using d.isOpenMap hr hC hΩ hcont Set.univ isOpen_univ

end OpenCoordinateData

omit [CompleteSpace X] in
/-- A normalized distance approximation with error at most half the pair's
distance separates the pair.  The scale may depend on both points. -/
theorem injOn_of_normalized_separation {Ω : Set X} {f : X → E}
    (N : ℕ → X → E ≃L[ℝ] E)
    (hsep : ∀ x ∈ Ω, ∀ z ∈ Ω, x ≠ z → ∃ i,
      |‖N i x (f z - f x)‖ - dist x z| ≤ dist x z / 2) : Set.InjOn f Ω := by
  intro x hx z hz heq
  by_contra hne
  obtain ⟨i, hi⟩ := hsep x hx z hz hne
  have hd : 0 < dist x z := dist_pos.mpr hne
  rw [← heq, sub_self, map_zero, norm_zero, zero_sub, abs_neg,
    abs_of_nonneg dist_nonneg] at hi
  linarith

/-- The complete constructive conclusion, with the homeomorphism equal to the
given coordinate map and its image proved open. -/
theorem open_homeomorph_of_normalized_separation
    {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω)
    (hsep : ∀ x ∈ Ω, ∀ z ∈ Ω, x ≠ z → ∃ i,
      |‖d.normalization i x (f z - f x)‖ - dist x z| ≤ dist x z / 2) :
    IsOpen (Set.range (fun x : Ω => f x)) ∧
      ∃ e : Ω ≃ₜ Set.range (fun x : Ω => f x), ∀ x, (e x).val = f x := by
  refine ⟨d.isOpen_range hr hC hΩ hcont,
    d.homeomorph hr hC hΩ hcont (injOn_of_normalized_separation d.normalization hsep), ?_⟩
  intro x
  rfl

end OpenImage

end RegularPointCoordinates

end OAI
