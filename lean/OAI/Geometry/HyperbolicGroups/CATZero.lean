import Mathlib
import OAI.Geometry.HyperbolicGroups.Basic

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap

noncomputable section
namespace HyperbolicObstruction
namespace CATZero

variable {X : Type*} [MetricSpace X]

/-- The comparison segment chosen from the CAT(0) comparison condition. -/
def segment (h : CATZero X) (x y : X) : ℝ → X := (h x y).choose

theorem segment_spec (h : CATZero X) (x y : X) :
    IsSegment (segment h x y) x y := (h x y).choose_spec.1

theorem segment_cn (h : CATZero X) (x y z : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist z (segment h x y t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 :=
  (h x y).choose_spec.2 z t ht

theorem segment_left (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist x (segment h x y t) = t * dist x y := by
  have hs := (segment_spec h x y).2.2 0 (by norm_num) t ht
  rw [(segment_spec h x y).1] at hs
  simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hs

theorem segment_right (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y t) y = (1 - t) * dist x y := by
  have hs := (segment_spec h x y).2.2 t ht 1 (by norm_num)
  rw [(segment_spec h x y).2.1] at hs
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hs
  simpa only [neg_sub] using hs

/-- CAT(0) comparison applies to any point with the prescribed division
    distances, rather than just to the initially chosen segment. -/
theorem eq_segment_of_dist (h : CATZero X) {x y p : X} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x p = t * dist x y)
    (hy : dist p y = (1 - t) * dist x y) :
    p = segment h x y t := by
  have hc := segment_cn h x y p ht
  rw [dist_comm p x, hx, hy] at hc
  have hz : dist p (segment h x y t) ^ 2 ≤ 0 := by nlinarith [hc]
  have hn : 0 ≤ dist p (segment h x y t) := dist_nonneg
  exact dist_eq_zero.mp (by nlinarith)

theorem cn_of_dist (h : CATZero X) {x y p : X} (z : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x p = t * dist x y)
    (hy : dist p y = (1 - t) * dist x y) :
    dist z p ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
      t * (1 - t) * dist x y ^ 2 := by
  rw [eq_segment_of_dist h ht hx hy]
  exact segment_cn h x y z ht

/-- Metric midpoint, available without completeness or properness. -/
def mid (h : CATZero X) (x y : X) : X := segment h x y (1 / 2)

theorem dist_left_mid (h : CATZero X) (x y : X) :
    dist x (mid h x y) = dist x y / 2 := by
  simpa [mid, div_eq_mul_inv, mul_comm] using segment_left h x y (t := 1 / 2) (by norm_num)

theorem dist_mid_right (h : CATZero X) (x y : X) :
    dist (mid h x y) y = dist x y / 2 := by
  have hs := segment_right h x y (t := 1 / 2) (by norm_num)
  norm_num at hs
  simpa [mid, div_eq_mul_inv, mul_comm] using hs

theorem mid_cn (h : CATZero X) (x y z : X) :
    dist z (mid h x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  have hc := segment_cn h x y z (t := 1 / 2) (by norm_num)
  dsimp [mid]
  linarith [hc]

/-- Source Lemma `energy:quadrilateral`, with its midpoint error retained. -/
theorem quadrilateral (h : CATZero X) (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 + 4 * dist (mid h a c) (mid h b d) ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  have hb := mid_cn h a c b
  have hd := mid_cn h a c d
  have hm := mid_cn h b d (mid h a c)
  rw [dist_comm b (mid h a c), dist_comm b a] at hb
  rw [dist_comm d (mid h a c), dist_comm d c] at hd
  linarith

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction

/-- The metric description of nonnegative radial dilations in a Euclidean
cone, with the angular cosine eliminated by polarization. No linear or
associative addition is included. -/
structure ConeData (X : Type*) [MetricSpace X] where
  vertex : X
  scale : ℝ → X → X
  scale_zero : ∀ x, scale 0 x = vertex
  scale_one : ∀ x, scale 1 x = x
  radial_metric : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → ∀ x y : X,
    dist (scale r x) (scale s y) ^ 2 =
      (r ^ 2 - r * s) * dist vertex x ^ 2 +
      (s ^ 2 - r * s) * dist vertex y ^ 2 + r * s * dist x y ^ 2

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

def normSq (x : X) : ℝ := dist T.vertex x ^ 2

def pairing (x y : X) : ℝ := (T.normSq x + T.normSq y - dist x y ^ 2) / 2

theorem normSq_nonneg (x : X) : 0 ≤ T.normSq x := sq_nonneg _

theorem pairing_comm (x y : X) : T.pairing x y = T.pairing y x := by
  simp only [pairing, dist_comm x y]
  ring

@[simp] theorem pairing_self (x : X) : T.pairing x x = T.normSq x := by
  simp [pairing]

@[simp] theorem normSq_vertex : T.normSq T.vertex = 0 := by simp [normSq]

@[simp] theorem pairing_vertex (x : X) : T.pairing T.vertex x = 0 := by
  simp [pairing, normSq]

theorem dist_sq (x y : X) :
    dist x y ^ 2 = T.normSq x + T.normSq y - 2 * T.pairing x y := by
  dsimp [pairing]
  ring

theorem normSq_scale {r : ℝ} (hr : 0 ≤ r) (x : X) :
    T.normSq (T.scale r x) = r ^ 2 * T.normSq x := by
  have hc := T.radial_metric r 0 hr (by norm_num) x x
  simpa [T.scale_zero, normSq, dist_comm] using hc

theorem pairing_scale {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (x y : X) :
    T.pairing (T.scale r x) (T.scale s y) = r * s * T.pairing x y := by
  unfold pairing
  rw [T.normSq_scale hr, T.normSq_scale hs, T.radial_metric r s hr hs]
  dsimp [normSq]
  ring

theorem pairing_scale_left {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.pairing (T.scale r x) y = r * T.pairing x y := by
  simpa [T.scale_one] using T.pairing_scale hr (show (0 : ℝ) ≤ 1 by norm_num) x y

theorem pairing_scale_right {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.pairing x (T.scale r y) = r * T.pairing x y := by
  rw [T.pairing_comm, T.pairing_scale_left hr, T.pairing_comm y x]

/-- In a CAT(0) Euclidean cone, comparison towards the vertex is an equality.
The reverse bound is obtained by comparing towards twice the division point;
no flat-sector theorem is assumed. -/
theorem normSq_segment (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.normSq (CATZero.segment h x y t) =
      (1 - t) * T.normSq x + t * T.normSq y - t * (1 - t) * dist x y ^ 2 := by
  let p := CATZero.segment h x y t
  have hp : p = CATZero.segment h x y t := rfl
  have hleft := CATZero.segment_left h x y ht
  have hright := CATZero.segment_right h x y ht
  have lower := CATZero.segment_cn h x y T.vertex ht
  have upper := CATZero.segment_cn h x y (T.scale 2 p) ht
  have hpp := T.radial_metric 2 1 (by norm_num) (by norm_num) p p
  have hpx := T.radial_metric 2 1 (by norm_num) (by norm_num) p x
  have hpy := T.radial_metric 2 1 (by norm_num) (by norm_num) p y
  simp only [T.scale_one, dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero] at hpp
  simp only [T.scale_one] at hpx hpy
  rw [dist_comm p x, hp, hleft] at hpx
  rw [hp, hright] at hpy
  change T.normSq p ≤ _ at lower
  change dist (T.scale 2 p) p ^ 2 ≤ _ at upper
  rw [hpp, hpx, hpy] at upper
  dsimp only [normSq, p] at *
  nlinarith [lower, upper]


@[simp] theorem normSq_eq_zero (x : X) : T.normSq x = 0 ↔ x = T.vertex := by
  simp [normSq, dist_eq_zero, eq_comm]

@[simp] theorem scale_vertex {r : ℝ} (hr : 0 ≤ r) :
    T.scale r T.vertex = T.vertex := by
  apply (T.normSq_eq_zero _).mp
  rw [T.normSq_scale hr, T.normSq_vertex, mul_zero]

theorem scale_mul {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (x : X) :
    T.scale r (T.scale s x) = T.scale (r * s) x := by
  have hd := T.dist_sq (T.scale r (T.scale s x)) (T.scale (r * s) x)
  rw [T.normSq_scale hr, T.normSq_scale hs, T.normSq_scale (mul_nonneg hr hs),
    T.pairing_scale hr (mul_nonneg hr hs), T.pairing_scale_left hs,
    T.pairing_self] at hd
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist (T.scale r (T.scale s x)) (T.scale (r * s) x))]

/-- Scalar-product concavity, derived directly from CN and radial equality. -/
theorem pairing_segment (h : CATZero X) (w x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * T.pairing w x + t * T.pairing w y ≤
      T.pairing w (CATZero.segment h x y t) := by
  have hc := CATZero.segment_cn h x y w ht
  unfold pairing
  rw [T.normSq_segment h x y ht]
  nlinarith [hc]

/-- The manuscript's two-vector cone addition (not an associative operation). -/
def add (h : CATZero X) (x y : X) : X := T.scale 2 (CATZero.mid h x y)

theorem normSq_mid (h : CATZero X) (x y : X) :
    T.normSq (CATZero.mid h x y) =
      (T.normSq x + T.normSq y) / 2 - dist x y ^ 2 / 4 := by
  have hm := T.normSq_segment h x y (t := 1 / 2) (by norm_num)
  change T.normSq (CATZero.mid h x y) = _ at hm
  linarith

theorem normSq_add (h : CATZero X) (x y : X) :
    T.normSq (T.add h x y) = T.normSq x + T.normSq y + 2 * T.pairing x y := by
  unfold add
  rw [T.normSq_scale (by norm_num), T.normSq_mid h, T.dist_sq x y]
  ring

theorem pairing_add_left (h : CATZero X) (x y : X) :
    T.pairing x (T.add h x y) = T.normSq x + T.pairing x y := by
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  unfold pairing
  rw [T.normSq_mid h, CATZero.dist_left_mid h]
  ring

theorem pairing_add_right (h : CATZero X) (x y : X) :
    T.pairing y (T.add h x y) = T.pairing x y + T.normSq y := by
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  unfold pairing
  rw [T.normSq_mid h, dist_comm y (CATZero.mid h x y), CATZero.dist_mid_right h]
  ring

/-- Source Equation `geom:sum-concavity`. -/
theorem pairing_add (h : CATZero X) (w x y : X) :
    T.pairing w x + T.pairing w y ≤ T.pairing w (T.add h x y) := by
  have hc := T.pairing_segment h w x y (t := 1 / 2) (by norm_num)
  change (1 - (1 / 2 : ℝ)) * T.pairing w x + (1 / 2 : ℝ) * T.pairing w y ≤
    T.pairing w (CATZero.mid h x y) at hc
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  linarith

/-- Normalized antipodal vectors sum to the cone vertex. -/
theorem add_antipodes (h : CATZero X) {c d : X}
    (hc : T.normSq c = 1) (hd : T.normSq d = 1)
    (hcd : T.pairing c d = -1) : T.add h c d = T.vertex := by
  apply (T.normSq_eq_zero _).mp
  rw [T.normSq_add h, hc, hd, hcd]
  norm_num

/-- The polar inequality of an isometrically embedded line. -/
theorem antipodal_pairing (h : CATZero X) {c d : X}
    (hc : T.normSq c = 1) (hd : T.normSq d = 1)
    (hcd : T.pairing c d = -1) (x : X) :
    T.pairing c x + T.pairing d x ≤ 0 := by
  have ha := T.pairing_add h x c d
  rw [T.add_antipodes h hc hd hcd, T.pairing_comm x T.vertex,
    T.pairing_vertex, T.pairing_comm x c, T.pairing_comm x d] at ha
  exact ha


@[simp] theorem add_vertex (h : CATZero X) (x : X) :
    T.add h x T.vertex = x := by
  have hn := T.normSq_add h x T.vertex
  have hp := T.pairing_add_left h x T.vertex
  rw [T.pairing_comm x T.vertex, T.pairing_vertex] at hn hp
  rw [T.normSq_vertex] at hn
  have hd := T.dist_sq x (T.add h x T.vertex)
  rw [hn, hp] at hd
  symm
  exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := T.add h x T.vertex)])

/-- Equal-length opposite points of a cone. The zero pair is permitted. -/
def Opposite (c d : X) : Prop :=
  T.normSq c = T.normSq d ∧ T.pairing c d = -T.normSq c

theorem Opposite.symm {c d : X} (hop : T.Opposite c d) : T.Opposite d c := by
  refine ⟨hop.1.symm, ?_⟩
  rw [T.pairing_comm, hop.2, hop.1]

theorem add_opposite (h : CATZero X) {c d : X} (hop : T.Opposite c d) :
    T.add h c d = T.vertex := by
  apply (T.normSq_eq_zero _).mp
  rw [T.normSq_add h, hop.2, ← hop.1]
  ring

theorem opposite_pairing (h : CATZero X) {c d : X} (hop : T.Opposite c d) (x : X) :
    T.pairing c x + T.pairing d x ≤ 0 := by
  have ha := T.pairing_add h x c d
  rw [T.add_opposite h hop, T.pairing_comm x T.vertex, T.pairing_vertex,
    T.pairing_comm x c, T.pairing_comm x d] at ha
  exact ha

/-- The zero set of the sum of the two Busemann coordinates of an axis.
All splitting identities used below are proved from CN, not assumed. -/
def Parallel (c d x : X) : Prop := T.pairing c x + T.pairing d x = 0

theorem Parallel.symm {c d x : X} (hx : T.Parallel c d x) : T.Parallel d c x := by
  unfold Parallel at *
  linarith

def translate (h : CATZero X) (c : X) (t : ℝ) (x : X) : X :=
  T.add h x (T.scale t c)

theorem normSq_translate (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.normSq (T.translate h c t x) =
      T.normSq x + t ^ 2 * T.normSq c + 2 * t * T.pairing c x := by
  unfold translate
  rw [T.normSq_add h, T.normSq_scale ht, T.pairing_scale_right ht,
    T.pairing_comm x c]
  ring

theorem pairing_translate_base (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing x (T.translate h c t x) = T.normSq x + t * T.pairing c x := by
  unfold translate
  rw [T.pairing_add_left h, T.pairing_scale_right ht, T.pairing_comm x c]

theorem pairing_translate_axis (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing c (T.translate h c t x) = T.pairing c x + t * T.normSq c := by
  rcases eq_or_lt_of_le ht with he | hpos
  · subst t
    simp [translate, T.scale_zero, T.add_vertex]
  · have hp := T.pairing_add_right h x (T.scale t c)
    rw [T.pairing_scale_left ht, T.pairing_scale_right ht, T.normSq_scale ht,
      T.pairing_comm x c] at hp
    change t * T.pairing c (T.translate h c t x) = _ at hp
    nlinarith

theorem pairing_translate_ge (h : CATZero X) (c x w : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing w x + t * T.pairing w c ≤ T.pairing w (T.translate h c t x) := by
  have hp := T.pairing_add h w x (T.scale t c)
  rwa [T.pairing_scale_right ht] at hp

/-- Translating towards either end of an axis preserves its parallel set. -/
theorem parallel_translate (h : CATZero X) {c d x : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) {t : ℝ} (ht : 0 ≤ t) :
    T.Parallel c d (T.translate h c t x) := by
  have hz := T.opposite_pairing h hop (T.translate h c t x)
  have hp := T.pairing_translate_ge h c x d ht
  rw [T.pairing_comm d c, hop.2] at hp
  unfold Parallel at hx ⊢
  rw [T.pairing_translate_axis h c x ht] at hz ⊢
  nlinarith

/-- The two cone translations are inverse on the parallel set. -/
theorem translate_inverse (h : CATZero X) {c d x : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) {t : ℝ} (ht : 0 ≤ t) :
    T.translate h d t (T.translate h c t x) = x := by
  have hyp := T.parallel_translate h hop hx ht
  have hyc := T.pairing_translate_axis h c x ht
  have hy := T.normSq_translate h c x ht
  have hz := T.normSq_translate h d (T.translate h c t x) ht
  have hzx := T.pairing_translate_ge h d (T.translate h c t x) x ht
  rw [T.pairing_translate_base h c x ht, T.pairing_comm x d] at hzx
  have hd := T.dist_sq x (T.translate h d t (T.translate h c t x))
  unfold Parallel at hx hyp
  rw [← hop.1] at hz
  have hnorm : T.normSq (T.translate h d t (T.translate h c t x)) = T.normSq x := by
    nlinarith
  rw [hnorm] at hd
  symm
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := T.translate h d t (T.translate h c t x))]

/-- Exact scalar-product translation formula on the parallel set. It is the
needed parallel-set splitting identity, proved without a product theorem. -/
theorem pairing_translate (h : CATZero X) {c d x y : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) (hy : T.Parallel c d y) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing x (T.translate h c t y) = T.pairing x y + t * T.pairing c x := by
  have hlo := T.pairing_translate_ge h c y x ht
  have hhi := T.pairing_translate_ge h d (T.translate h c t y) x ht
  rw [T.translate_inverse h hop hy ht, T.pairing_comm x d] at hhi
  rw [T.pairing_comm x c] at hlo
  unfold Parallel at hx
  nlinarith


theorem add_comm (h : CATZero X) (x y : X) : T.add h x y = T.add h y x := by
  have hm : CATZero.mid h y x = CATZero.mid h x y := by
    apply CATZero.eq_segment_of_dist h (t := 1 / 2) (by norm_num)
    · rw [dist_comm x (CATZero.mid h y x), CATZero.dist_mid_right h, dist_comm y x]
      ring
    · rw [dist_comm (CATZero.mid h y x) y, CATZero.dist_left_mid h, dist_comm y x]
      ring
  unfold add
  rw [hm]

theorem pairing_translates_same (h : CATZero X) {c d x y : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) (hy : T.Parallel c d y)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.pairing (T.translate h c s x) (T.translate h c t y) =
      T.pairing x y + s * T.pairing c y + t * T.pairing c x +
        s * t * T.normSq c := by
  rw [T.pairing_translate h hop (T.parallel_translate h hop hx hs) hy ht,
    T.pairing_comm (T.translate h c s x) y, T.pairing_translate h hop hy hx hs,
    T.pairing_translate_axis h c x hs, T.pairing_comm y x]
  ring

theorem pairing_translates_opposite (h : CATZero X) {c d x y : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) (hy : T.Parallel c d y)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.pairing (T.translate h c s x) (T.translate h d t y) =
      T.pairing x y + s * T.pairing c y - t * T.pairing c x -
        s * t * T.normSq c := by
  have hpx := T.parallel_translate h hop hx hs
  have hc := T.pairing_translate_axis h c x hs
  rw [T.pairing_translate h (hop.symm T) (hpx.symm T) (hy.symm T) ht,
    T.pairing_comm (T.translate h c s x) y, T.pairing_translate h hop hy hx hs,
    T.pairing_comm y x]
  unfold Parallel at hpx
  nlinarith

/-- Opposite orthogonal pairs have opposite cone sums. This is a small
flat-square rigidity statement, using the proved translation identity. -/
theorem opposite_add_of_orthogonal (h : CATZero X) {u u' v v' : X}
    (hu : T.Opposite u u') (hv : T.Opposite v v')
    (huv : T.pairing u v = 0) (huv' : T.pairing u v' = 0)
    (hu'v : T.pairing u' v = 0) (hu'v' : T.pairing u' v' = 0) :
    T.Opposite (T.add h u v) (T.add h u' v') := by
  have hpv : T.Parallel u u' v := by simp [Parallel, huv, hu'v]
  have hpv' : T.Parallel u u' v' := by simp [Parallel, huv', hu'v']
  have hp := T.pairing_translates_opposite h hu hpv hpv'
    (s := 1) (t := 1) (by norm_num) (by norm_num)
  simp only [translate, T.scale_one, one_mul, mul_one, huv, huv', hv.2,
    T.add_comm h v u, T.add_comm h v' u'] at hp
  constructor
  · rw [T.normSq_add h, T.normSq_add h, huv, hu'v', hu.1, hv.1]
  · rw [hp, T.normSq_add h, huv]
    ring

/-- Unit vectors satisfy the lower Cauchy bound without any ambient linear
structure. This is just the triangle inequality of the cone. -/
theorem pairing_unit_lower {x y : X} (hx : T.normSq x = 1) (hy : T.normSq y = 1) :
    -1 ≤ T.pairing x y := by
  have hnx : dist T.vertex x = 1 := by
    dsimp [normSq] at hx
    nlinarith [dist_nonneg (x := T.vertex) (y := x)]
  have hny : dist T.vertex y = 1 := by
    dsimp [normSq] at hy
    nlinarith [dist_nonneg (x := T.vertex) (y := y)]
  have hd := dist_triangle x T.vertex y
  rw [dist_comm x T.vertex, hnx, hny] at hd
  unfold pairing
  rw [hx, hy]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Source Lemma `geom:antipodal`, in an algebraic form that avoids a
local-to-global theorem in the completed space of directions. -/
theorem exceptional_antipodes (h : CATZero X) {c d x y z : X}
    (hc : T.normSq c = 1) (hd : T.normSq d = 1)
    (hdy : T.pairing d y = 1 / 2) (hdx : T.pairing d x = 1 / 2)
    (hyz : T.Opposite y z) (hz : z = T.add h c x) : T.Opposite c d := by
  have hp := T.opposite_pairing h hyz d
  rw [T.pairing_comm y d, T.pairing_comm z d, hdy] at hp
  have hs := T.pairing_add h d c x
  rw [← hz, hdx, T.pairing_comm d c] at hs
  have hlo := T.pairing_unit_lower hc hd
  constructor
  · rw [hc, hd]
  · rw [hc]
    linarith


theorem eq_of_normSq_pairing {x y : X} (hn : T.normSq x = T.normSq y)
    (hp : T.normSq x ≤ T.pairing x y) : x = y := by
  have hd := T.dist_sq x y
  rw [← hn] at hd
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem pairing_add_add (h : CATZero X) (x y u v : X) :
    T.pairing x u + T.pairing x v + T.pairing y u + T.pairing y v ≤
      T.pairing (T.add h x y) (T.add h u v) := by
  have ha := T.pairing_add h (T.add h u v) x y
  have hx := T.pairing_add h x u v
  have hy := T.pairing_add h y u v
  rw [T.pairing_comm (T.add h u v) x, T.pairing_comm (T.add h u v) y,
    T.pairing_comm (T.add h u v) (T.add h x y)] at ha
  linarith

theorem add_eq_of_pairings (h : CATZero X) {x y u v : X}
    (hn : T.normSq (T.add h x y) = T.normSq (T.add h u v))
    (hp : T.normSq (T.add h x y) ≤
      T.pairing x u + T.pairing x v + T.pairing y u + T.pairing y v) :
    T.add h x y = T.add h u v :=
  T.eq_of_normSq_pairing hn (hp.trans (T.pairing_add_add h x y u v))

/-- The transverse-square conclusion used in the final obstruction. The
four original vectors are not assumed to lie in a plane or a vector space. -/
theorem opposite_cross_sums (h : CATZero X) {p q r s : X}
    (hnp : T.normSq p = 3 / 4) (hnq : T.normSq q = 3 / 4)
    (hnr : T.normSq r = 3 / 4) (hns : T.normSq s = 3 / 4)
    (hpq : T.pairing p q = -1 / 4) (hpr : T.pairing p r = -1 / 4)
    (hps : T.pairing p s = -1 / 4) (hqr : T.pairing q r = -1 / 4)
    (hqs : T.pairing q s = -1 / 4) (hrs : T.pairing r s = -1 / 4)
    (hop : T.Opposite (T.add h p q) (T.add h r s)) :
    T.Opposite (T.add h p r) (T.add h q s) := by
  let c := T.add h p q
  let d := T.add h r s
  change T.Opposite c d at hop
  have hc : T.normSq c = 1 := by simp [c, T.normSq_add, hnp, hnq, hpq]; norm_num
  have hd : T.normSq d = 1 := by simp [d, T.normSq_add, hnr, hns, hrs]; norm_num
  have hcp : T.pairing c p = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [c]; rw [T.pairing_add_left, hnp, hpq]; norm_num
  have hcq : T.pairing c q = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [c]; rw [T.pairing_add_right, hnq, hpq]; norm_num
  have hdr : T.pairing d r = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [d]; rw [T.pairing_add_left, hnr, hrs]; norm_num
  have hds : T.pairing d s = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [d]; rw [T.pairing_add_right, hns, hrs]; norm_num
  have hcr : T.pairing c r = -1 / 2 := by
    have hlo := T.pairing_add h r p q
    rw [T.pairing_comm r p, T.pairing_comm r q, hpr, hqr,
      T.pairing_comm r (T.add h p q)] at hlo
    have hhi := T.opposite_pairing h hop r
    rw [hdr] at hhi
    change _ ≤ T.pairing c r at hlo
    linarith
  have hcs : T.pairing c s = -1 / 2 := by
    have hlo := T.pairing_add h s p q
    rw [T.pairing_comm s p, T.pairing_comm s q, hps, hqs,
      T.pairing_comm s (T.add h p q)] at hlo
    have hhi := T.opposite_pairing h hop s
    rw [hds] at hhi
    change _ ≤ T.pairing c s at hlo
    linarith
  have hdp : T.pairing d p = -1 / 2 := by
    have hlo := T.pairing_add h p r s
    rw [hpr, hps, T.pairing_comm p (T.add h r s)] at hlo
    have hhi := T.opposite_pairing h hop p
    rw [hcp] at hhi
    change _ ≤ T.pairing d p at hlo
    linarith
  have hdq : T.pairing d q = -1 / 2 := by
    have hlo := T.pairing_add h q r s
    rw [hqr, hqs, T.pairing_comm q (T.add h r s)] at hlo
    have hhi := T.opposite_pairing h hop q
    rw [hcq] at hhi
    change _ ≤ T.pairing d q at hlo
    linarith
  have hpp : T.Parallel c d p := by norm_num [Parallel, hcp, hdp]
  have hpq' : T.Parallel c d q := by norm_num [Parallel, hcq, hdq]
  have hpr' : T.Parallel c d r := by norm_num [Parallel, hcr, hdr]
  have hps' : T.Parallel c d s := by norm_num [Parallel, hcs, hds]
  let u := T.translate h d (1 / 2) p
  let u' := T.translate h d (1 / 2) q
  let v := T.translate h c (1 / 2) r
  let v' := T.translate h c (1 / 2) s
  have hnu : T.normSq u = 1 / 2 := by
    dsimp [u]; rw [T.normSq_translate h d p (by norm_num), hnp, hd, hdp]; norm_num
  have hnu' : T.normSq u' = 1 / 2 := by
    dsimp [u']; rw [T.normSq_translate h d q (by norm_num), hnq, hd, hdq]; norm_num
  have hnv : T.normSq v = 1 / 2 := by
    dsimp [v]; rw [T.normSq_translate h c r (by norm_num), hnr, hc, hcr]; norm_num
  have hnv' : T.normSq v' = 1 / 2 := by
    dsimp [v']; rw [T.normSq_translate h c s (by norm_num), hns, hc, hcs]; norm_num
  have huu' : T.pairing u u' = -1 / 2 := by
    dsimp [u, u']
    rw [T.pairing_translates_same h (hop.symm T) (hpp.symm T) (hpq'.symm T)
      (by norm_num) (by norm_num), hpq, hdp, hdq, hd]
    norm_num
  have hvv' : T.pairing v v' = -1 / 2 := by
    dsimp [v, v']
    rw [T.pairing_translates_same h hop hpr' hps' (by norm_num) (by norm_num),
      hrs, hcr, hcs, hc]
    norm_num
  have huv : T.pairing u v = 0 := by
    dsimp [u, v]
    rw [T.pairing_translates_opposite h (hop.symm T) (hpp.symm T) (hpr'.symm T)
      (by norm_num) (by norm_num), hpr, hdp, hdr, hd]
    norm_num
  have huv' : T.pairing u v' = 0 := by
    dsimp [u, v']
    rw [T.pairing_translates_opposite h (hop.symm T) (hpp.symm T) (hps'.symm T)
      (by norm_num) (by norm_num), hps, hdp, hds, hd]
    norm_num
  have hu'v : T.pairing u' v = 0 := by
    dsimp [u', v]
    rw [T.pairing_translates_opposite h (hop.symm T) (hpq'.symm T) (hpr'.symm T)
      (by norm_num) (by norm_num), hqr, hdq, hdr, hd]
    norm_num
  have hu'v' : T.pairing u' v' = 0 := by
    dsimp [u', v']
    rw [T.pairing_translates_opposite h (hop.symm T) (hpq'.symm T) (hps'.symm T)
      (by norm_num) (by norm_num), hqs, hdq, hds, hd]
    norm_num
  have hu : T.Opposite u u' := by constructor <;> norm_num [hnu, hnu', huu']
  have hv : T.Opposite v v' := by constructor <;> norm_num [hnv, hnv', hvv']
  have ha : T.add h p r = T.add h u v := by
    apply T.add_eq_of_pairings h
    · norm_num [T.normSq_add, hnp, hnr, hpr, hnu, hnv, huv]
    · have hpu := T.pairing_translate h (hop.symm T) (hpp.symm T) (hpp.symm T)
        (t := 1 / 2) (by norm_num)
      have hpv := T.pairing_translate h hop hpp hpr' (t := 1 / 2) (by norm_num)
      have hru := T.pairing_translate h (hop.symm T) (hpr'.symm T) (hpp.symm T)
        (t := 1 / 2) (by norm_num)
      have hrv := T.pairing_translate h hop hpr' hpr' (t := 1 / 2) (by norm_num)
      change T.pairing p u = _ at hpu
      change T.pairing p v = _ at hpv
      change T.pairing r u = _ at hru
      change T.pairing r v = _ at hrv
      rw [T.normSq_add, hnp, hnr, hpr, hpu, hpv, hru, hrv,
        T.pairing_self, T.pairing_self, hnp, hdp, hpr, hcp, T.pairing_comm r p,
        hpr, hdr, hnr, hcr]
      norm_num
  have hb : T.add h q s = T.add h u' v' := by
    apply T.add_eq_of_pairings h
    · norm_num [T.normSq_add, hnq, hns, hqs, hnu', hnv', hu'v']
    · have hqu := T.pairing_translate h (hop.symm T) (hpq'.symm T) (hpq'.symm T)
        (t := 1 / 2) (by norm_num)
      have hqv := T.pairing_translate h hop hpq' hps' (t := 1 / 2) (by norm_num)
      have hsu := T.pairing_translate h (hop.symm T) (hps'.symm T) (hpq'.symm T)
        (t := 1 / 2) (by norm_num)
      have hsv := T.pairing_translate h hop hps' hps' (t := 1 / 2) (by norm_num)
      change T.pairing q u' = _ at hqu
      change T.pairing q v' = _ at hqv
      change T.pairing s u' = _ at hsu
      change T.pairing s v' = _ at hsv
      rw [T.normSq_add, hnq, hns, hqs, hqu, hqv, hsu, hsv,
        T.pairing_self, T.pairing_self, hnq, hdq, hqs, hcq, T.pairing_comm s q,
        hqs, hds, hns, hcs]
      norm_num
  rw [ha, hb]
  exact T.opposite_add_of_orthogonal h hu hv huv huv' hu'v hu'v'


/-- Final algebraic contradiction in Proposition `prop:no-configuration`.
The five line indices are AB, AC, AD, BC, BD, respectively. All geometric
input here is explicit; no Hilbert-space or associativity assumption is used. -/
theorem five_line_fans_contradiction (h : CATZero X) (ℓ : Fin 5 → X)
    (hn : ∀ i, T.normSq (ℓ i) = 3 / 4)
    (hp : ∀ i j, i ≠ j → T.pairing (ℓ i) (ℓ j) = -1 / 4)
    (hA : T.add h (ℓ 0) (ℓ 1) = T.add h (ℓ 1) (ℓ 2))
    (hB : T.add h (ℓ 0) (ℓ 3) = T.add h (ℓ 3) (ℓ 4))
    (hop : T.Opposite (T.add h (ℓ 1) (ℓ 3)) (T.add h (ℓ 2) (ℓ 4))) : False := by
  have hcross := T.opposite_cross_sums h (hn 1) (hn 3) (hn 2) (hn 4)
    (hp 1 3 (by decide)) (hp 1 2 (by decide)) (hp 1 4 (by decide))
    (hp 3 2 (by decide)) (hp 3 4 (by decide)) (hp 2 4 (by decide)) hop
  have hnorm : T.normSq (T.add h (ℓ 1) (ℓ 2)) = 1 := by
    rw [T.normSq_add, hn 1, hn 2, hp 1 2 (by decide)]
    norm_num
  have hneg := hcross.2
  rw [hnorm] at hneg
  have hpos := T.pairing_add_add h (ℓ 0) (ℓ 1) (ℓ 0) (ℓ 3)
  rw [T.pairing_self, hn 0, hp 0 3 (by decide), hp 1 0 (by decide),
    hp 1 3 (by decide), hA, hB] at hpos
  linarith

end ConeData
end HyperbolicObstruction

noncomputable section

end
end
end
end
end
end

end OAI
