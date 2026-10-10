import Mathlib
import OAI.Geometry.HyperbolicGroups.CATZero

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem segment_dist (h : CATZero X) (x y : X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y s) (segment h x y t) = |s - t| * dist x y :=
  (segment_spec h x y).2.2 s hs t ht

theorem segment_mul (h : CATZero X) (x y : X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segment h x (segment h x y t) s = segment h x y (s * t) := by
  have hst : s * t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hs.1 ht.1, by nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hs.2) ht.1]⟩
  symm
  apply eq_segment_of_dist h hs
  · rw [segment_left h x y hst, segment_left h x y ht]
    ring
  · rw [segment_dist h x y hst ht, segment_left h x y ht,
      abs_of_nonpos (by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) ht.1])]
    ring

/-- Radial contraction, used in the construction of the tangent pseudometric. -/
theorem radial_contraction (h : CATZero X) (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h o x t) (segment h o y t) ≤ t * dist x y := by
  have ha := segment_cn h o y (segment h o x t) ht
  have hb := segment_cn h o x y ht
  rw [dist_comm (segment h o x t) o, segment_left h o x ht,
    dist_comm (segment h o x t) y] at ha
  rw [dist_comm y o, dist_comm y x] at hb
  have hab : dist (segment h o x t) (segment h o y t) ^ 2 ≤ t ^ 2 * dist x y ^ 2 := by
    nlinarith [mul_nonneg ht.1
      (show 0 ≤ (1 - t) * dist o y ^ 2 + t * dist x y ^ 2 -
        t * (1 - t) * dist o x ^ 2 - dist y (segment h o x t) ^ 2 by linarith)]
  nlinarith [dist_nonneg (x := segment h o x t) (y := segment h o y t),
    mul_nonneg ht.1 (dist_nonneg (x := x) (y := y))]

/-- A comparison scalar product at two positive positions on radial segments.
Its supremum as the positions decrease is the tangent scalar product. -/
def radialPairing (h : CATZero X) (o x y : X) (a b : ℝ) : ℝ :=
  (a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 -
    dist (segment h o x a) (segment h o y b) ^ 2) / (2 * a * b)

theorem radialPairing_comm (h : CATZero X) (o x y : X) (a b : ℝ) :
    radialPairing h o x y a b = radialPairing h o y x b a := by
  unfold radialPairing
  rw [dist_comm (segment h o x a) (segment h o y b)]
  ring

theorem radialPairing_lower (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    -(dist o x * dist o y) ≤ radialPairing h o x y a b := by
  have hd := dist_triangle (segment h o x a) o (segment h o y b)
  rw [dist_comm (segment h o x a) o, segment_left h o x ⟨ha.1.le, ha.2⟩,
    segment_left h o y ⟨hb.1.le, hb.2⟩] at hd
  unfold radialPairing
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) ha.1) hb.1)).mpr
  have hn := dist_nonneg (x := segment h o x a) (y := segment h o y b)
  have hs : dist (segment h o x a) (segment h o y b) ^ 2 ≤
      (a * dist o x + b * dist o y) ^ 2 := by
    nlinarith [hd, hn]
  nlinarith [hs]

theorem radialPairing_upper (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a b ≤ dist o x * dist o y := by
  have hdx := dist_triangle o (segment h o y b) (segment h o x a)
  have hdy := dist_triangle o (segment h o x a) (segment h o y b)
  rw [segment_left h o x ⟨ha.1.le, ha.2⟩, segment_left h o y ⟨hb.1.le, hb.2⟩,
    dist_comm (segment h o y b) (segment h o x a)] at hdx
  rw [segment_left h o x ⟨ha.1.le, ha.2⟩, segment_left h o y ⟨hb.1.le, hb.2⟩] at hdy
  unfold radialPairing
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) ha.1) hb.1)).mpr
  have hs : (a * dist o x - b * dist o y) ^ 2 ≤
      dist (segment h o x a) (segment h o y b) ^ 2 := by
    have hp := mul_nonneg
      (show 0 ≤ dist (segment h o x a) (segment h o y b) -
        (a * dist o x - b * dist o y) by linarith)
      (show 0 ≤ dist (segment h o x a) (segment h o y b) +
        (a * dist o x - b * dist o y) by linarith)
    nlinarith
  nlinarith [hs]

/-- Comparison products increase when either point moves towards the base. -/
theorem radialPairing_antitone_left (h : CATZero X) (o x y : X)
    {a a' b : ℝ} (ha : 0 < a) (haa : a ≤ a') (ha' : a' ≤ 1)
    (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a' b ≤ radialPairing h o x y a b := by
  have hap : 0 < a' := lt_of_lt_of_le ha haa
  have ht : a / a' ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos ha hap).le, (div_le_one hap).mpr haa⟩
  have hc := segment_cn h o (segment h o x a') (segment h o y b) ht
  rw [segment_mul h o x ht ⟨hap.le, ha'⟩, div_mul_cancel₀ a hap.ne',
    dist_comm (segment h o y b) o, segment_left h o y ⟨hb.1.le, hb.2⟩,
    segment_left h o x ⟨hap.le, ha'⟩,
    dist_comm (segment h o y b) (segment h o x a),
    dist_comm (segment h o y b) (segment h o x a')] at hc
  unfold radialPairing
  apply (div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hap) hb.1)
    (mul_pos (mul_pos (by norm_num) ha) hb.1)).mpr
  have hc' := mul_le_mul_of_nonneg_left hc hap.le
  field_simp at hc'
  nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hc')]

theorem radialPairing_antitone_right (h : CATZero X) (o x y : X)
    {a b b' : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (hbb : b ≤ b') (hb' : b' ≤ 1) :
    radialPairing h o x y a b' ≤ radialPairing h o x y a b := by
  rw [radialPairing_comm h o x y a b', radialPairing_comm h o x y a b]
  exact radialPairing_antitone_left h o y x hb hbb hb' ha

/-- Definition by bounded supremum, so no completeness of the ambient CAT(0)
space is required to form comparison products in its tangent cone. -/
def tangentPairing (h : CATZero X) (o x y : X) : ℝ :=
  sSup {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
    v = radialPairing h o x y a b}

theorem tangentPairing_set_nonempty (h : CATZero X) (o x y : X) :
    Set.Nonempty {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
      v = radialPairing h o x y a b} :=
  ⟨_, 1, by norm_num, 1, by norm_num, rfl⟩

theorem tangentPairing_set_bddAbove (h : CATZero X) (o x y : X) :
    BddAbove {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
      v = radialPairing h o x y a b} := by
  refine ⟨dist o x * dist o y, ?_⟩
  rintro v ⟨a, ha, b, hb, rfl⟩
  exact radialPairing_upper h o x y ha hb

theorem radialPairing_le_tangentPairing (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a b ≤ tangentPairing h o x y :=
  le_csSup (tangentPairing_set_bddAbove h o x y) ⟨a, ha, b, hb, rfl⟩

theorem tangentPairing_upper (h : CATZero X) (o x y : X) :
    tangentPairing h o x y ≤ dist o x * dist o y := by
  apply csSup_le (tangentPairing_set_nonempty h o x y)
  rintro v ⟨a, ha, b, hb, rfl⟩
  exact radialPairing_upper h o x y ha hb

theorem tangentPairing_lower (h : CATZero X) (o x y : X) :
    -(dist o x * dist o y) ≤ tangentPairing h o x y :=
  (radialPairing_lower h o x y (a := 1) (b := 1) (by norm_num) (by norm_num)).trans
    (radialPairing_le_tangentPairing h o x y (by norm_num) (by norm_num))

theorem tangentPairing_comm (h : CATZero X) (o x y : X) :
    tangentPairing h o x y = tangentPairing h o y x := by
  unfold tangentPairing
  congr 1
  ext v
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩
  · exact ⟨b, hb, a, ha, radialPairing_comm h o x y a b⟩
  · exact ⟨b, hb, a, ha, radialPairing_comm h o y x a b⟩

theorem tangentPairing_self (h : CATZero X) (o x : X) :
    tangentPairing h o x x = dist o x ^ 2 := by
  apply le_antisymm
  · simpa only [pow_two] using tangentPairing_upper h o x x
  · have hl := radialPairing_le_tangentPairing h o x x (a := 1) (b := 1)
      (by norm_num) (by norm_num)
    simpa [radialPairing] using hl

theorem tangentPairing_vertex (h : CATZero X) (o x : X) :
    tangentPairing h o o x = 0 := by
  have hl := tangentPairing_lower h o o x
  have hu := tangentPairing_upper h o o x
  simp only [dist_self, zero_mul, neg_zero] at hl hu
  exact le_antisymm hu hl

open Filter Topology

theorem radialPairing_tendsto (h : CATZero X) (o x y : X)
    {ι : Type*} {F : Filter ι} {a b : ι → ℝ}
    (ha : Tendsto a F (𝓝 0)) (hb : Tendsto b F (𝓝 0))
    (hap : ∀ᶠ i in F, 0 < a i) (hbp : ∀ᶠ i in F, 0 < b i) :
    Tendsto (fun i => radialPairing h o x y (a i) (b i)) F
      (𝓝 (tangentPairing h o x y)) := by
  apply tendsto_order.mpr
  constructor
  · intro v hv
    obtain ⟨w, ⟨a', ha', b', hb', rfl⟩, hvw⟩ :=
      exists_lt_of_lt_csSup (tangentPairing_set_nonempty h o x y) hv
    filter_upwards [hap, hbp, ha.eventually (gt_mem_nhds ha'.1),
      hb.eventually (gt_mem_nhds hb'.1)] with i hai hbi hai' hbi'
    exact hvw.trans_le ((radialPairing_antitone_left h o x y hai hai'.le ha'.2 hb').trans
      (radialPairing_antitone_right h o x y ⟨hai, hai'.le.trans ha'.2⟩
        hbi hbi'.le hb'.2))
  · intro v hv
    filter_upwards [hap, hbp, ha.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hb.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hai hbi hai' hbi'
    exact (radialPairing_le_tangentPairing h o x y ⟨hai, hai'.le⟩ ⟨hbi, hbi'.le⟩).trans_lt hv

/-- Distance between formal nonnegative multiples of two radial directions. -/
def tangentDist (h : CATZero X) (o x y : X) (r s : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
    2 * r * s * tangentPairing h o x y)

theorem tangentDist_sq_nonneg (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * tangentPairing h o x y := by
  have hh := tangentPairing_upper h o x y
  nlinarith [mul_nonneg (mul_nonneg hr hs) (sub_nonneg.mpr hh),
    sq_nonneg (r * dist o x - s * dist o y)]

theorem tangentDist_sq (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    tangentDist h o x y r s ^ 2 = r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * tangentPairing h o x y :=
  Real.sq_sqrt (tangentDist_sq_nonneg h o x y hr hs)

theorem tangentDist_comm (h : CATZero X) (o x y : X) (r s : ℝ) :
    tangentDist h o x y r s = tangentDist h o y x s r := by
  unfold tangentDist
  rw [tangentPairing_comm h o x y]
  congr 1
  ring

@[simp] theorem tangentDist_zero_left (h : CATZero X) (o x y : X) {s : ℝ}
    (hs : 0 ≤ s) : tangentDist h o x y 0 s = s * dist o y := by
  unfold tangentDist
  have he : (0 : ℝ) ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * 0 * s * tangentPairing h o x y = (s * dist o y) ^ 2 := by ring
  rw [he, Real.sqrt_sq (mul_nonneg hs dist_nonneg)]

@[simp] theorem tangentDist_zero_right (h : CATZero X) (o x y : X) {r : ℝ}
    (hr : 0 ≤ r) : tangentDist h o x y r 0 = r * dist o x := by
  rw [tangentDist_comm, tangentDist_zero_left h o y x hr]

theorem tangentDist_tendsto_pos (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * r)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y r s)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  have hts : Tendsto (fun t : ℝ => t * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const s
  have hp := radialPairing_tendsto h o x y htr hts
    (htp.mono fun _ hx => mul_pos hx hr) (htp.mono fun _ hx => mul_pos hx hs)
  have hl : Tendsto (fun t : ℝ => Real.sqrt
      (r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
        2 * r * s * radialPairing h o x y (t * r) (t * s))) (𝓝[>] 0)
      (𝓝 (tangentDist h o x y r s)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)).sqrt
  apply hl.congr'
  filter_upwards [htp] with t htp'
  unfold radialPairing
  have he : r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * (( (t * r) ^ 2 * dist o x ^ 2 + (t * s) ^ 2 * dist o y ^ 2 -
        dist (segment h o x (t * r)) (segment h o y (t * s)) ^ 2) /
          (2 * (t * r) * (t * s))) =
      (dist (segment h o x (t * r)) (segment h o y (t * s)) / t) ^ 2 := by
    field_simp
    ring
  rw [he, Real.sqrt_sq (div_nonneg dist_nonneg htp'.le)]

theorem tangentDist_tendsto_zero_left (h : CATZero X) (o x y : X) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * 0)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y 0 s)) := by
  rw [tangentDist_zero_left h o x y hs]
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hts : Tendsto (fun t : ℝ => t * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const s
  apply tendsto_const_nhds.congr'
  filter_upwards [htp, hts.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t htp' hts'
  rw [mul_zero, (segment_spec h o x).1,
    segment_left h o y ⟨mul_nonneg htp'.le hs, hts'⟩]
  field_simp

theorem tangentDist_tendsto (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * r)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y r s)) := by
  rcases eq_or_lt_of_le hr with he | hr
  · subst r
    exact tangentDist_tendsto_zero_left h o x y hs
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simpa only [dist_comm, tangentDist_comm h o x y r 0] using
      tangentDist_tendsto_zero_left h o y x hr.le
  exact tangentDist_tendsto_pos h o x y hr hs

theorem tangentDist_triangle (h : CATZero X) (o x y z : X) {r s t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    tangentDist h o x z r t ≤ tangentDist h o x y r s + tangentDist h o y z s t := by
  apply le_of_tendsto_of_tendsto (tangentDist_tendsto h o x z hr ht)
    ((tangentDist_tendsto h o x y hr hs).add (tangentDist_tendsto h o y z hs ht))
  filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from eventually_mem_nhdsWithin]
    with a ha
  simpa only [add_div] using div_le_div_of_nonneg_right
    (dist_triangle (segment h o x (a * r)) (segment h o y (a * s))
      (segment h o z (a * t))) ha.le

theorem tangentDist_same (h : CATZero X) (o x : X) (r s : ℝ) :
    tangentDist h o x x r s = |r - s| * dist o x := by
  unfold tangentDist
  rw [tangentPairing_self]
  have he : r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o x ^ 2 -
      2 * r * s * dist o x ^ 2 = ((r - s) * dist o x) ^ 2 := by ring
  rw [he, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg dist_nonneg]

theorem tangentDist_quadrilateral (h : CATZero X) (o a b c d : X)
    {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    tangentDist h o a c r t ^ 2 + tangentDist h o b d s u ^ 2 ≤
      tangentDist h o a b r s ^ 2 + tangentDist h o b c s t ^ 2 +
        tangentDist h o c d t u ^ 2 + tangentDist h o d a u r ^ 2 := by
  apply le_of_tendsto_of_tendsto
    (((tangentDist_tendsto h o a c hr ht).pow 2).add
      ((tangentDist_tendsto h o b d hs hu).pow 2))
    (((((tangentDist_tendsto h o a b hr hs).pow 2).add
      ((tangentDist_tendsto h o b c hs ht).pow 2)).add
      ((tangentDist_tendsto h o c d ht hu).pow 2)).add
      ((tangentDist_tendsto h o d a hu hr).pow 2))
  filter_upwards [show ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < k from eventually_mem_nhdsWithin]
    with k hk
  have hq := quadrilateral h (segment h o a (k * r)) (segment h o b (k * s))
    (segment h o c (k * t)) (segment h o d (k * u))
  have hq' : dist (segment h o a (k * r)) (segment h o c (k * t)) ^ 2 +
      dist (segment h o b (k * s)) (segment h o d (k * u)) ^ 2 ≤
      dist (segment h o a (k * r)) (segment h o b (k * s)) ^ 2 +
      dist (segment h o b (k * s)) (segment h o c (k * t)) ^ 2 +
      dist (segment h o c (k * t)) (segment h o d (k * u)) ^ 2 +
      dist (segment h o d (k * u)) (segment h o a (k * r)) ^ 2 := by
    nlinarith [sq_nonneg (dist
      (mid h (segment h o a (k * r)) (segment h o c (k * t)))
      (mid h (segment h o b (k * s)) (segment h o d (k * u))))]
  simpa only [div_pow, add_div] using div_le_div_of_nonneg_right hq' (sq_nonneg k)

theorem tangentDist_radial_left (h : CATZero X) (o x y : X) {a r s : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    tangentDist h o (segment h o x a) y r s = tangentDist h o x y (r * a) s := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  have he : (fun t : ℝ =>
      dist (segment h o (segment h o x a) (t * r)) (segment h o y (t * s)) / t)
      =ᶠ[𝓝[>] 0] (fun t : ℝ =>
      dist (segment h o x (t * (r * a))) (segment h o y (t * s)) / t) := by
    filter_upwards [htp, htr.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht' htr'
    rw [segment_mul h o x ⟨mul_nonneg ht'.le hr, htr'⟩ ha, mul_assoc]
  exact tendsto_nhds_unique ((tangentDist_tendsto h o (segment h o x a) y hr hs).congr' he)
    (tangentDist_tendsto h o x y (mul_nonneg hr ha.1) hs)

theorem tangentDist_radial_right (h : CATZero X) (o x y : X) {a r s : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    tangentDist h o x (segment h o y a) r s = tangentDist h o x y r (s * a) := by
  rw [tangentDist_comm, tangentDist_radial_left h o y x ha hs hr, tangentDist_comm]

/-- Metric form of the log comparison, for any common radial factor. -/
theorem tangentDist_le (h : CATZero X) (o x y : X) {r : ℝ} (hr : 0 ≤ r) :
    tangentDist h o x y r r ≤ r * dist x y := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  apply le_of_tendsto_of_tendsto (tangentDist_tendsto h o x y hr hr) tendsto_const_nhds
  filter_upwards [htp, htr.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t ht' htr'
  apply (div_le_iff₀ ht').mpr
  calc
    dist (segment h o x (t * r)) (segment h o y (t * r)) ≤ (t * r) * dist x y :=
      radial_contraction h o x y ⟨mul_nonneg ht'.le hr, htr'⟩
    _ = (r * dist x y) * t := by ring

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

/-- Represented directions with an arbitrary nonnegative radial length factor.
Zero-distance representatives are identified by the Hausdorff completion. -/
structure TangentRay (h : CATZero X) (o : X) where
  weight : ℝ≥0
  point : X

namespace TangentRay
variable (h : CATZero X) (o : X)

instance : PseudoMetricSpace (TangentRay h o) where
  dist p q := CATZero.tangentDist h o p.point q.point p.weight q.weight
  dist_self p := by rw [CATZero.tangentDist_same]; simp
  dist_comm p q := CATZero.tangentDist_comm h o p.point q.point p.weight q.weight
  dist_triangle p q r := CATZero.tangentDist_triangle h o p.point q.point r.point
    p.weight.coe_nonneg q.weight.coe_nonneg r.weight.coe_nonneg

def vertex : TangentRay h o := ⟨0, o⟩
def log (x : X) : TangentRay h o := ⟨1, x⟩
def scale (r : ℝ≥0) (p : TangentRay h o) : TangentRay h o := ⟨r * p.weight, p.point⟩

theorem dist_def (p q : TangentRay h o) :
    dist p q = CATZero.tangentDist h o p.point q.point p.weight q.weight := rfl

theorem dist_sq (p q : TangentRay h o) :
    dist p q ^ 2 = (p.weight : ℝ) ^ 2 * dist o p.point ^ 2 +
      (q.weight : ℝ) ^ 2 * dist o q.point ^ 2 -
        2 * (p.weight : ℝ) * (q.weight : ℝ) * CATZero.tangentPairing h o p.point q.point :=
  CATZero.tangentDist_sq h o p.point q.point p.weight.coe_nonneg q.weight.coe_nonneg

theorem dist_vertex (p : TangentRay h o) :
    dist (vertex h o) p = (p.weight : ℝ) * dist o p.point :=
  CATZero.tangentDist_zero_left h o o p.point p.weight.coe_nonneg

theorem radial_metric (r s : ℝ≥0) (p q : TangentRay h o) :
    dist (scale h o r p) (scale h o s q) ^ 2 =
      ((r : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) p ^ 2 +
      ((s : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) q ^ 2 +
      (r : ℝ) * (s : ℝ) * dist p q ^ 2 := by
  rw [dist_sq, dist_vertex, dist_vertex, dist_sq]
  dsimp only [scale, NNReal.coe_mul]
  ring

theorem dist_scale (r : ℝ≥0) (p q : TangentRay h o) :
    dist (scale h o r p) (scale h o r q) = (r : ℝ) * dist p q := by
  have he := radial_metric h o r r p q
  have hn := dist_nonneg (x := scale h o r p) (y := scale h o r q)
  have hn' := mul_nonneg r.coe_nonneg (dist_nonneg (x := p) (y := q))
  nlinarith

theorem scale_lipschitz (r : ℝ≥0) : LipschitzWith r (scale h o r) :=
  LipschitzWith.of_dist_le_mul fun p q => (dist_scale h o r p q).le

theorem quadrilateral (a b c d : TangentRay h o) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 :=
  CATZero.tangentDist_quadrilateral h o a.point b.point c.point d.point
    a.weight.coe_nonneg b.weight.coe_nonneg c.weight.coe_nonneg d.weight.coe_nonneg

end TangentRay

/-- The completed cone of represented directions, built from radial CAT(0)
comparison limits rather than postulated to exist. -/
abbrev TangentCone (h : CATZero X) (o : X) := Completion (TangentRay h o)


end HyperbolicObstruction
end
end
end
end
end
end
end

end OAI
