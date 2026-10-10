import Mathlib
import OAI.Geometry.HyperbolicGroups.TangentCone

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace HyperbolicObstruction
open Filter Topology

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

/-- The constructed completed tangent cone is CAT(0). -/
theorem catZero : CATZero (TangentCone h o) :=
  catZero_of_midpoints (coneMid h o) (coneMid_left h o) (coneMid_cn h o)

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

/-- Two-vector affine combinations in a metric cone agree with its metric
segments; associativity has not been assumed. -/
theorem segment_eq_add_scale (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CATZero.segment h x y t = T.add h (T.scale (1 - t) x) (T.scale t y) := by
  let z := T.add h (T.scale (1 - t) x) (T.scale t y)
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hn := T.normSq_add h (T.scale (1 - t) x) (T.scale t y)
  rw [T.normSq_scale ht', T.normSq_scale ht.1, T.pairing_scale ht' ht.1] at hn
  have hpx := T.pairing_add h x (T.scale (1 - t) x) (T.scale t y)
  rw [T.pairing_scale_right ht', T.pairing_scale_right ht.1, T.pairing_self] at hpx
  have hpy := T.pairing_add h y (T.scale (1 - t) x) (T.scale t y)
  rw [T.pairing_scale_right ht', T.pairing_scale_right ht.1, T.pairing_self,
    T.pairing_comm y x] at hpy
  have hxz := T.dist_sq x z
  have hyz := T.dist_sq y z
  have hxy := T.dist_sq x y
  change T.normSq z = _ at hn
  change _ ≤ T.pairing x z at hpx
  change _ ≤ T.pairing y z at hpy
  have hx : dist x z ≤ t * dist x y := by
    nlinarith [mul_nonneg ht.1 (dist_nonneg (x := x) (y := y)),
      dist_nonneg (x := x) (y := z)]
  have hy : dist z y ≤ (1 - t) * dist x y := by
    rw [dist_comm]
    nlinarith [mul_nonneg ht' (dist_nonneg (x := x) (y := y)),
      dist_nonneg (x := y) (y := z)]
  have htri := dist_triangle x z y
  symm
  exact CATZero.eq_segment_of_dist h ht (by linarith) (by linarith)

theorem parallel_scale {c d x : X} (hx : T.Parallel c d x) {r : ℝ} (hr : 0 ≤ r) :
    T.Parallel c d (T.scale r x) := by
  unfold Parallel at hx ⊢
  rw [T.pairing_scale_right hr, T.pairing_scale_right hr]
  nlinarith

/-- Distance between opposite translations of one point in the parallel set. -/
theorem dist_opposite_translates_sq (h : CATZero X) {c d x : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    dist (T.translate h c r x) (T.translate h d s x) ^ 2 =
      (r + s) ^ 2 * T.normSq c := by
  have hpx := T.parallel_translate h hop hx hr
  have hp := T.pairing_translate h hop.symm hpx.symm hx.symm hs
  rw [T.pairing_comm (T.translate h c r x) x, T.pairing_translate_base h c x hr] at hp
  have ha := T.pairing_translate_axis h c x hr
  unfold Parallel at hx hpx
  rw [T.dist_sq, T.normSq_translate h c x hr, T.normSq_translate h d x hs, hp, ← hop.1]
  nlinarith

theorem dist_opposite_segments_sq (h : CATZero X) {c d x : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (CATZero.segment h x c t) (CATZero.segment h x d t) ^ 2 = t ^ 2 * dist c d ^ 2 := by
  rw [T.segment_eq_add_scale h x c ht, T.segment_eq_add_scale h x d ht]
  change dist (T.translate h c t (T.scale (1 - t) x))
    (T.translate h d t (T.scale (1 - t) x)) ^ 2 = _
  rw [T.dist_opposite_translates_sq h hop (T.parallel_scale hx (sub_nonneg.mpr ht.2)) ht.1 ht.1,
    T.dist_sq c d, hop.2, ← hop.1]
  ring

end ConeData

namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- Restricting a chosen CAT(0) segment gives the chosen segment, including
reversed subsegments. -/
theorem segment_between (h : CATZero X) (x y : X) {s u t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segment h (segment h x y s) (segment h x y u) t =
      segment h x y ((1 - t) * s + t * u) := by
  have hm : (1 - t) * s + t * u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hs.1) (mul_nonneg ht.1 hu.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ht.1 (sub_nonneg.mpr hu.2)]
  symm
  apply eq_segment_of_dist h ht
  · rw [(segment_spec h x y).2.2 s hs _ hm, (segment_spec h x y).2.2 s hs u hu]
    rw [show s - ((1 - t) * s + t * u) = t * (s - u) by ring, abs_mul,
      abs_of_nonneg ht.1]
    ring
  · rw [(segment_spec h x y).2.2 _ hm u hu, (segment_spec h x y).2.2 s hs u hu]
    rw [show (1 - t) * s + t * u - u = (1 - t) * (s - u) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
    ring

/-- A nonexpanding map that preserves one endpoint distance preserves the
whole parametrized segment between those endpoints. -/
theorem map_segment_of_dist {Y : Type*} [MetricSpace Y] (hX : CATZero X) (hY : CATZero Y)
    (f : X → Y) (hf : ∀ a b, dist (f a) (f b) ≤ dist a b)
    (x y : X) (hxy : dist (f x) (f y) = dist x y) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (segment hX x y t) = segment hY (f x) (f y) t := by
  have hx := hf x (segment hX x y t)
  have hy := hf (segment hX x y t) y
  rw [segment_left hX x y ht, ← hxy] at hx
  rw [segment_right hX x y ht, ← hxy] at hy
  have htri := dist_triangle (f x) (f (segment hX x y t)) (f y)
  exact eq_segment_of_dist hY ht (by linarith) (by linarith)

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- The log based at any point of a segment is distance preserving on that
segment, including pairs lying on opposite sides of the basepoint. -/
theorem log_dist_on_segment (x y : X) {v s u : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    dist (log h (CATZero.segment h x y v) (CATZero.segment h x y s))
      (log h (CATZero.segment h x y v) (CATZero.segment h x y u)) =
        dist (CATZero.segment h x y s) (CATZero.segment h x y u) := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h (CATZero.segment h x y v)
    (CATZero.segment h x y s) (CATZero.segment h x y u) 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h (CATZero.segment h x y v)
    (CATZero.segment h x y s) (CATZero.segment h x y u) (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, CATZero.segment_between h x y hv hs ⟨ht0.le, ht1⟩,
    CATZero.segment_between h x y hv hu ⟨ht0.le, ht1⟩]
  have hv' (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      (1 - t) * v + t * a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hv.1) (mul_nonneg ht0.le ha.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hv.2),
        mul_nonneg ht0.le (sub_nonneg.mpr ha.2)]
  rw [(CATZero.segment_spec h x y).2.2 _ (hv' s hs) _ (hv' u hu),
    (CATZero.segment_spec h x y).2.2 s hs u hu,
    show (1 - t) * v + t * s - ((1 - t) * v + t * u) = t * (s - u) by ring,
    abs_mul, abs_of_pos ht0]
  field_simp

theorem log_dist_mid_endpoints (x y : X) :
    dist (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y) = dist x y := by
  have he := log_dist_on_segment h x y
    (v := 1 / 2) (s := 0) (u := 1) (by norm_num) (by norm_num) (by norm_num)
  change dist (log h (CATZero.mid h x y) (CATZero.segment h x y 0))
    (log h (CATZero.mid h x y) (CATZero.segment h x y 1)) =
      dist (CATZero.segment h x y 0) (CATZero.segment h x y 1) at he
  rw [(CATZero.segment_spec h x y).1, (CATZero.segment_spec h x y).2.1] at he
  exact he

theorem opposite_mid_logs (x y : X) :
    (coneData h (CATZero.mid h x y)).Opposite
      (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y) := by
  constructor
  · rw [normSq_log, normSq_log, CATZero.dist_mid_right,
      dist_comm (CATZero.mid h x y) x, CATZero.dist_left_mid]
  · unfold ConeData.pairing
    rw [normSq_log, normSq_log, log_dist_mid_endpoints, CATZero.dist_mid_right,
      dist_comm (CATZero.mid h x y) x, CATZero.dist_left_mid]
    ring

theorem pairing_log_ge (o x y : X) :
    (dist o x ^ 2 + dist o y ^ 2 - dist x y ^ 2) / 2 ≤
      (coneData h o).pairing (log h o x) (log h o y) := by
  have hd := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (dist_log_le h o x y)
  unfold ConeData.pairing
  rw [normSq_log, normSq_log]
  linarith

/-- Equality in the original midpoint CN comparison puts the opposite
endpoint logs and the third log in their common parallel set, and the log
preserves both remaining triangle sides. -/
theorem midpoint_equality_parallel (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    (coneData h (CATZero.mid h x y)).Parallel
      (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y)
        (log h (CATZero.mid h x y) o) ∧
    dist (log h (CATZero.mid h x y) o) (log h (CATZero.mid h x y) x) = dist o x ∧
    dist (log h (CATZero.mid h x y) o) (log h (CATZero.mid h x y) y) = dist o y := by
  let m := CATZero.mid h x y
  let T := coneData h m
  let H := catZero h m
  have hop := opposite_mid_logs h x y
  have hc := T.opposite_pairing H hop (log h m o)
  have hx := pairing_log_ge h m x o
  have hy := pairing_log_ge h m y o
  have hmx : dist m x = dist x y / 2 := by
    rw [dist_comm]; exact CATZero.dist_left_mid h x y
  have hmy : dist m y = dist x y / 2 := CATZero.dist_mid_right h x y
  have hmo : dist m o ^ 2 = (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4 := by
    rwa [dist_comm] at heq
  rw [hmx, hmo, dist_comm x o] at hx
  rw [hmy, hmo, dist_comm y o] at hy
  have hpar : T.Parallel (log h m x) (log h m y) (log h m o) := by
    unfold ConeData.Parallel
    dsimp only [T] at hc ⊢
    linarith
  refine ⟨hpar, ?_, ?_⟩
  · have hd := T.dist_sq (log h m x) (log h m o)
    dsimp only [T] at hd
    rw [normSq_log, normSq_log, hmx, hmo, dist_comm (log h m x) (log h m o)] at hd
    nlinarith [dist_nonneg (x := log h m o) (y := log h m x), dist_nonneg (x := o) (y := x)]
  · have hd := T.dist_sq (log h m y) (log h m o)
    dsimp only [T] at hd
    rw [normSq_log, normSq_log, hmy, hmo, dist_comm (log h m y) (log h m o)] at hd
    nlinarith [dist_nonneg (x := log h m o) (y := log h m y), dist_nonneg (x := o) (y := y)]

/-- The radial distance consequence of flat-triangle rigidity, proved via the
parallel set of the opposite logs at the midpoint. -/
theorem radial_distance_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (CATZero.segment h o x t) (CATZero.segment h o y t) = t * dist x y := by
  obtain ⟨hpar, hx, hy⟩ := midpoint_equality_parallel h o x y heq
  let m := CATZero.mid h x y
  let T := coneData h m
  let H := catZero h m
  have he := T.dist_opposite_segments_sq H (opposite_mid_logs h x y) hpar ht
  rw [← CATZero.map_segment_of_dist h H (log h m) (dist_log_le h m) o x hx ht,
    ← CATZero.map_segment_of_dist h H (log h m) (dist_log_le h m) o y hy ht,
    log_dist_mid_endpoints] at he
  have hlo := dist_log_le h m (CATZero.segment h o x t) (CATZero.segment h o y t)
  have hhi := CATZero.radial_contraction h o x y ht
  have hlo' := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr hlo
  rw [he] at hlo'
  nlinarith [mul_nonneg ht.1 (dist_nonneg (x := x) (y := y)),
    dist_nonneg (x := CATZero.segment h o x t) (y := CATZero.segment h o y t)]

/-- The tangent log preserves the base side of a triangle with midpoint CN
equality. This is the exact flat-triangle transfer needed by the obstruction. -/
theorem log_dist_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    dist (log h o x) (log h o y) = dist x y := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h o x y 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h o x y (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, radial_distance_of_midpoint_equality h o x y heq ⟨ht0.le, ht1⟩]
  field_simp

theorem log_mid_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    log h o (CATZero.mid h x y) = CATZero.mid (catZero h o) (log h o x) (log h o y) :=
  CATZero.map_segment_of_dist h (catZero h o) (log h o) (dist_log_le h o) x y
    (log_dist_of_midpoint_equality h o x y heq) (by norm_num)

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem segment_reverse (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segment h y x (1 - t) = segment h x y t := by
  have hs := segment_between h x y (s := 1) (u := 0) (t := 1 - t)
    (by norm_num) (by norm_num) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [(segment_spec h x y).1, (segment_spec h x y).2.1,
    sub_sub_cancel, mul_one, mul_zero, add_zero] using hs

theorem mid_swap (h : CATZero X) (x y : X) : mid h y x = mid h x y := by
  have he := segment_reverse h x y (t := 1 / 2) (by norm_num)
  norm_num at he
  exact he

/-- A CN equality at any nontrivial interior point implies equality at the
midpoint. The proof uses only convexity on the appropriate half-segment. -/
theorem midpoint_equality_of_interior (h : CATZero X) (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (heq : dist o (segment h x y t) ^ 2 = (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 -
      t * (1 - t) * dist x y ^ 2) :
    dist o (mid h x y) ^ 2 = (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  have hhalf (a b : X) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1 / 2)
      (he : dist o (segment h a b s) ^ 2 = (1 - s) * dist o a ^ 2 + s * dist o b ^ 2 -
        s * (1 - s) * dist a b ^ 2) :
      dist o (mid h a b) ^ 2 = (dist o a ^ 2 + dist o b ^ 2) / 2 - dist a b ^ 2 / 4 := by
    have hc := segment_cn h a (mid h a b) o (t := 2 * s) ⟨by positivity, by linarith⟩
    have hsm : segment h a (mid h a b) (2 * s) = segment h a b s := by
      unfold mid
      rw [segment_mul h a b ⟨by positivity, by linarith⟩ (by norm_num)]
      congr 1
      ring
    rw [hsm, he, dist_left_mid] at hc
    apply le_antisymm (mid_cn h a b o)
    apply (mul_le_mul_iff_of_pos_left hs0).mp
    nlinarith
  by_cases htt : t ≤ 1 / 2
  · exact hhalf x y t ht.1 htt heq
  · have he : dist o (segment h y x (1 - t)) ^ 2 =
        (1 - (1 - t)) * dist o y ^ 2 + (1 - t) * dist o x ^ 2 -
          (1 - t) * (1 - (1 - t)) * dist y x ^ 2 := by
      rw [segment_reverse h x y ⟨ht.1.le, ht.2.le⟩, heq, dist_comm y x]
      ring
    have hh := hhalf y x (1 - t) (by linarith [ht.2]) (by linarith) he
    rw [mid_swap, dist_comm y x] at hh
    linarith

end CATZero

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

theorem log_dist_of_interior_equality (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (heq : dist o (CATZero.segment h x y t) ^ 2 =
      (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 - t * (1 - t) * dist x y ^ 2) :
    dist (log h o x) (log h o y) = dist x y :=
  log_dist_of_midpoint_equality h o x y (CATZero.midpoint_equality_of_interior h o x y ht heq)

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem dist_scale {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    dist (T.scale r x) (T.scale r y) = r * dist x y := by
  have he := T.radial_metric r r hr hr x y
  nlinarith [dist_nonneg (x := T.scale r x) (y := T.scale r y),
    mul_nonneg hr (dist_nonneg (x := x) (y := y))]

theorem scale_segment (h : CATZero X) {r : ℝ} (hr : 0 ≤ r) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.scale r (CATZero.segment h x y t) =
      CATZero.segment h (T.scale r x) (T.scale r y) t := by
  apply CATZero.eq_segment_of_dist h ht
  · rw [T.dist_scale hr, T.dist_scale hr, CATZero.segment_left h x y ht]
    ring
  · rw [T.dist_scale hr, T.dist_scale hr, CATZero.segment_right h x y ht]
    ring

theorem scale_add (h : CATZero X) {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.scale r (T.add h x y) = T.add h (T.scale r x) (T.scale r y) := by
  unfold add
  rw [T.scale_mul hr (by norm_num), mul_comm r 2,
    ← T.scale_mul (by norm_num) hr, CATZero.mid,
    T.scale_segment h hr x y (by norm_num)]
  rfl

end ConeData

namespace TangentCone
open Filter Topology UniformSpace
variable {X : Type*} [MetricSpace X] (h : CATZero X)

theorem log_radial (o x : X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    log h o (CATZero.segment h o x t) = (coneData h o).scale t (log h o x) := by
  change log h o (CATZero.segment h o x t) = scaleN h o t.toNNReal (log h o x)
  rw [log, log, scaleN_coe]
  apply dist_eq_zero.mp
  rw [Completion.dist_eq, TangentRay.dist_def]
  dsimp only [TangentRay.log, TangentRay.scale, NNReal.coe_one, NNReal.coe_mul, mul_one]
  rw [Real.coe_toNNReal _ ht.1, mul_one,
    CATZero.tangentDist_radial_left h o x x ht (by norm_num) ht.1,
    one_mul, CATZero.tangentDist_same]
  simp

/-- Equality of distances at all sufficiently small radial fractions transfers
exactly to the completed tangent cone. -/
theorem log_dist_of_radial_equal (o x y : X)
    (heq : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      dist (CATZero.segment h o x t) (CATZero.segment h o y t) = t * dist x y) :
    dist (log h o x) (log h o y) = dist x y := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h o x y 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h o x y (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, heq t ⟨ht0, ht1⟩]
  field_simp

/-- The fixed-fraction angle test of the source suffices; no exchange of
ultralimits and angles is used. -/
theorem log_dist_of_right_fractional (o x y : X)
    (hsq : dist x y ^ 2 = dist o x ^ 2 + dist o y ^ 2)
    (hlower : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      t ^ 2 * (dist o x ^ 2 + dist o y ^ 2) ≤
        dist (CATZero.segment h o x t) (CATZero.segment h o y t) ^ 2) :
    dist (log h o x) (log h o y) = dist x y := by
  apply log_dist_of_radial_equal h o x y
  intro t ht
  have hc := CATZero.radial_contraction h o x y ⟨ht.1.le, ht.2⟩
  have hl := hlower t ht
  rw [← hsq] at hl
  nlinarith [mul_nonneg ht.1.le (dist_nonneg (x := x) (y := y)),
    dist_nonneg (x := CATZero.segment h o x t) (y := CATZero.segment h o y t)]

end TangentCone
end HyperbolicObstruction

noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
