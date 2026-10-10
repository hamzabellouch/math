import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeData

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
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- The midpoint part of square rigidity, retaining just the metric data
needed later. -/
theorem square_mid (h : CATZero X) {p q r s : X}
    (hpq : dist p q ^ 2 = 1) (hqr : dist q r ^ 2 = 1)
    (hrs : dist r s ^ 2 = 1) (hsp : dist s p ^ 2 = 1)
    (hpr : dist p r ^ 2 = 2) (hqs : dist q s ^ 2 = 2) :
    mid h p r = mid h q s := by
  have hq := quadrilateral h p q r s
  rw [hpq, hqr, hrs, hsp, hpr, hqs] at hq
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := mid h p r) (y := mid h q s)]

end CATZero
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- A log-isometric base gives every radial CN equality, directly from the
constructed cone metric law and uniqueness of segments. -/
theorem cn_eq_of_log_dist (o x y : X)
    (he : dist (log h o x) (log h o y) = dist x y) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist o (CATZero.segment h x y t) ^ 2 =
      (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  have hmap := CATZero.map_segment_of_dist h (catZero h o) (log h o)
    (dist_log_le h o) x y he ht
  have hn := (coneData h o).normSq_segment (catZero h o) (log h o x) (log h o y) ht
  rw [← hmap, normSq_log, normSq_log, normSq_log, he] at hn
  exact hn

/-- The fan midpoint identity, derived from a metric square and the central
flatness of its line diagonal. -/
theorem fan_identity (c x y a b : X)
    (hcx : dist c x ^ 2 = 3 / 4) (hcy : dist c y ^ 2 = 3 / 4)
    (hca : dist c a ^ 2 = 3 / 4) (hcb : dist c b ^ 2 = 3 / 4)
    (hxa : dist x a ^ 2 = 1) (hay : dist a y ^ 2 = 1)
    (hyb : dist y b ^ 2 = 1) (hbx : dist b x ^ 2 = 1)
    (hxy : dist x y ^ 2 = 2) (hab : dist a b ^ 2 = 2)
    (hflat : dist c (CATZero.mid h a b) ^ 2 = 1 / 4) :
    (coneData h c).pairing (log h c x) (log h c y) = -1 / 4 ∧
    (coneData h c).add (catZero h c) (log h c x) (log h c y) =
      (coneData h c).add (catZero h c) (log h c a) (log h c b) := by
  have hm := CATZero.square_mid h hxa hay hyb hbx hxy hab
  have heab : dist c (CATZero.mid h a b) ^ 2 =
      (dist c a ^ 2 + dist c b ^ 2) / 2 - dist a b ^ 2 / 4 := by
    rw [hca, hcb, hab, hflat]
    norm_num
  have hexy : dist c (CATZero.mid h x y) ^ 2 =
      (dist c x ^ 2 + dist c y ^ 2) / 2 - dist x y ^ 2 / 4 := by
    rw [hm, hflat, hcx, hcy, hxy]
    norm_num
  constructor
  · unfold ConeData.pairing
    rw [normSq_log, normSq_log, log_dist_of_midpoint_equality h c x y hexy, hcx, hcy, hxy]
    norm_num
  · unfold ConeData.add
    rw [← log_mid_of_midpoint_equality h c x y hexy,
      ← log_mid_of_midpoint_equality h c a b heab, hm]

/-- Source exceptional-incidence identity. Its hypotheses are entirely metric,
including the fixed-fraction test; no flat triangle or cone identity is assumed. -/
theorem exceptional_identity (c p q z k : X)
    (hcp : dist c p ^ 2 = 3 / 4) (hcq : dist c q ^ 2 = 3 / 4)
    (hcz : dist c z ^ 2 = 3 / 4) (hck : dist c k ^ 2 = 3 / 4)
    (hpq : dist p q ^ 2 = 2) (hpz : dist p z ^ 2 = 2) (hqz : dist q z ^ 2 = 2)
    (hcj : dist c (CATZero.mid h p q) ^ 2 = 1 / 4)
    (hkj : dist k (CATZero.mid h p q) ^ 2 = 1 / 2) (hkz : dist k z ^ 2 = 1)
    (hfrac : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      t ^ 2 * (1 / 2 + 1) ≤ dist (CATZero.segment h k (CATZero.mid h p q) t)
        (CATZero.segment h k z t) ^ 2) :
    log h c k = (coneData h c).add (catZero h c)
      ((coneData h c).add (catZero h c) (log h c p) (log h c q)) (log h c z) := by
  let j := CATZero.mid h p q
  let b := CATZero.segment h j z (1 / 3)
  have hjz : dist j z ^ 2 = 3 / 2 := by
    have hlo := hfrac 1 (by norm_num)
    rw [(CATZero.segment_spec h k j).2.1, (CATZero.segment_spec h k z).2.1] at hlo
    have hhi := CATZero.mid_cn h p q z
    rw [dist_comm z p, dist_comm z q, hpz, hqz, hpq, dist_comm z j] at hhi
    norm_num at hlo
    linarith
  have hlogk : dist (log h k j) (log h k z) = dist j z := by
    apply log_dist_of_right_fractional h k j z
    · rw [hjz, hkj, hkz]
      norm_num
    · intro t ht
      rw [hkj, hkz]
      exact hfrac t ht
  have hkb : dist k b ^ 2 = 1 / 3 := by
    have he := cn_eq_of_log_dist h k j z hlogk (t := 1 / 3) (by norm_num)
    rw [hkj, hkz, hjz] at he
    dsimp only [b]
    linarith
  have hcb : dist c b ^ 2 ≤ 1 / 12 := by
    have he := CATZero.segment_cn h j z c (t := 1 / 3) (by norm_num)
    rw [hcj, hcz, hjz] at he
    exact le_trans he (by norm_num)
  have hkbl : dist k b = 2 / 3 * dist c k := by
    nlinarith [dist_nonneg (x := k) (y := b), dist_nonneg (x := c) (y := k)]
  have hcbl : dist c b = 1 / 3 * dist c k := by
    have htri := dist_triangle c b k
    rw [dist_comm b k, hkbl] at htri
    nlinarith [dist_nonneg (x := c) (y := b), dist_nonneg (x := c) (y := k)]
  have hb : b = CATZero.segment h c k (1 / 3) := by
    apply CATZero.eq_segment_of_dist h (by norm_num)
    · exact hcbl
    · rw [dist_comm, hkbl]
      ring
  have hec : dist c b ^ 2 =
      (1 - 1 / 3) * dist c j ^ 2 + (1 / 3) * dist c z ^ 2 -
        (1 / 3) * (1 - 1 / 3) * dist j z ^ 2 := by
    rw [hcbl, hcj, hcz, hjz, mul_pow, hck]
    norm_num
  have hlogc := log_dist_of_interior_equality h c j z (t := 1 / 3) (by norm_num) hec
  have hmap := CATZero.map_segment_of_dist h (catZero h c) (log h c) (dist_log_le h c)
    j z hlogc (t := 1 / 3) (by norm_num)
  have hlogb : log h c b = (coneData h c).scale (1 / 3) (log h c k) := by
    rw [hb, log_radial h c k (by norm_num)]
  have hsum : log h c k = (coneData h c).add (catZero h c)
      ((coneData h c).scale 2 (log h c j)) (log h c z) := by
    have he := congrArg ((coneData h c).scale 3) hmap
    change (coneData h c).scale 3 (log h c b) = _ at he
    rw [hlogb, (coneData h c).scale_mul (by norm_num) (by norm_num)] at he
    norm_num only [show (3 : ℝ) * (1 / 3) = 1 by norm_num, (coneData h c).scale_one] at he
    rw [(coneData h c).segment_eq_add_scale (catZero h c) _ _ (by norm_num),
      (coneData h c).scale_add (catZero h c) (by norm_num),
      (coneData h c).scale_mul (by norm_num) (by norm_num),
      (coneData h c).scale_mul (by norm_num) (by norm_num)] at he
    norm_num at he
    simpa only [(coneData h c).scale_one] using he
  have hepq : dist c j ^ 2 = (dist c p ^ 2 + dist c q ^ 2) / 2 - dist p q ^ 2 / 4 := by
    rw [hcj, hcp, hcq, hpq]
    norm_num
  rw [hsum, log_mid_of_midpoint_equality h c p q hepq]
  rfl

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction

/-- Squared metric data for the unit square, in cyclic order. -/
structure MetricSquare {X : Type*} [MetricSpace X] (p q r s : X) : Prop where
  side₀ : dist p q ^ 2 = 1
  side₁ : dist q r ^ 2 = 1
  side₂ : dist r s ^ 2 = 1
  side₃ : dist s p ^ 2 = 1
  diagonal₀ : dist p r ^ 2 = 2
  diagonal₁ : dist q s ^ 2 = 2

theorem MetricSquare.mid_eq {X : Type*} [MetricSpace X] {p q r s : X}
    (hs : MetricSquare p q r s) (h : CATZero X) : CATZero.mid h p r = CATZero.mid h q s :=
  CATZero.square_mid h hs.side₀ hs.side₁ hs.side₂ hs.side₃ hs.diagonal₀ hs.diagonal₁

/-- Full incidences among the six lines AB, AC, AD, BC, BD, CD at A,B,C,D.
These are exactly the doubled fans of the source. -/
def fullLines : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4}]

/-- The specific subconfiguration used by the source obstruction. This is
metric input to a contradiction, not an assumed existence assertion. All its
conditions are consequences asserted by source Proposition `configuration`;
the existence-from-actions direction remains a separate obligation. -/
structure FiniteObstructionData {X : Type*} [MetricSpace X] (h : CATZero X) where
  c : X
  x : Fin 4 → X
  y : Fin 4 → X
  line : Fin 6 → X
  radiusX : ∀ i, dist c (x i) ^ 2 = 3 / 4
  radiusY : ∀ i, dist c (y i) ^ 2 = 3 / 4
  radiusLine : ∀ i, dist c (line i) ^ 2 = 3 / 4
  lineDist : ∀ a b, a ≠ b → dist (line a) (line b) ^ 2 = 2
  lineFlat : ∀ a b, a ≠ b → dist c (CATZero.mid h (line a) (line b)) ^ 2 = 1 / 4
  square : ∀ i a b, a ∈ fullLines i → b ∈ fullLines i → a ≠ b →
    MetricSquare (x i) (line a) (y i) (line b)
  twoStepX : dist (x 2) (x 3) ^ 2 = 2
  twoStepY : dist (y 2) (x 3) ^ 2 = 2
  loose : dist (line 5) (x 3) ^ 2 = 1
  missing : 3 ≤ dist (y 3) (line 5) ^ 2
  fractional : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    t ^ 2 * (1 / 2 + 1) ≤
      dist (CATZero.segment h (line 5) (CATZero.mid h (x 2) (y 2)) t)
        (CATZero.segment h (line 5) (x 3) t) ^ 2

/-- The complete finite CAT(0) metric obstruction from Section 6. The proof
constructs the completed tangent cone and all rigidity identities internally. -/
theorem no_finite_obstruction {X : Type*} [MetricSpace X] (h : CATZero X)
    (D : FiniteObstructionData h) : False := by
  let T := TangentCone.coneData h D.c
  let H := TangentCone.catZero h D.c
  let L : Fin 6 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.line i)
  let U : Fin 4 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.x i)
  let V : Fin 4 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.y i)
  let M : Fin 4 → TangentCone h D.c := fun i => T.add H (U i) (V i)
  have hnL (i) : T.normSq (L i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.line i)).trans (D.radiusLine i)
  have hnU (i) : T.normSq (U i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.x i)).trans (D.radiusX i)
  have hnV (i) : T.normSq (V i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.y i)).trans (D.radiusY i)
  have hpL (a b) (hne : a ≠ b) : T.pairing (L a) (L b) = -1 / 4 := by
    have he : dist D.c (CATZero.mid h (D.line a) (D.line b)) ^ 2 =
        (dist D.c (D.line a) ^ 2 + dist D.c (D.line b) ^ 2) / 2 -
          dist (D.line a) (D.line b) ^ 2 / 4 := by
      rw [D.lineFlat a b hne, D.radiusLine a, D.radiusLine b, D.lineDist a b hne]
      norm_num
    have hd := TangentCone.log_dist_of_midpoint_equality h D.c (D.line a) (D.line b) he
    change dist (L a) (L b) = _ at hd
    rw [ConeData.pairing, hnL, hnL, hd, D.lineDist a b hne]
    norm_num
  have hfan (i a b) (ha : a ∈ fullLines i) (hb : b ∈ fullLines i) (hne : a ≠ b) :
      T.pairing (U i) (V i) = -1 / 4 ∧ M i = T.add H (L a) (L b) := by
    have hs := D.square i a b ha hb hne
    exact TangentCone.fan_identity h D.c (D.x i) (D.y i) (D.line a) (D.line b)
      (D.radiusX i) (D.radiusY i) (D.radiusLine a) (D.radiusLine b)
      hs.side₀ hs.side₁ hs.side₂ hs.side₃ hs.diagonal₀ hs.diagonal₁ (D.lineFlat a b hne)
  have hA₁ := hfan 0 0 1 (by decide) (by decide) (by decide)
  have hA₂ := hfan 0 1 2 (by decide) (by decide) (by decide)
  have hB₁ := hfan 1 0 3 (by decide) (by decide) (by decide)
  have hB₂ := hfan 1 3 4 (by decide) (by decide) (by decide)
  have hC := hfan 2 1 3 (by decide) (by decide) (by decide)
  have hD := hfan 3 2 4 (by decide) (by decide) (by decide)
  have hnM₂ : T.normSq (M 2) = 1 := by
    change T.normSq (T.add H (U 2) (V 2)) = 1
    rw [T.normSq_add, hnU, hnV, hC.1]
    norm_num
  have hnM₃ : T.normSq (M 3) = 1 := by
    change T.normSq (T.add H (U 3) (V 3)) = 1
    rw [T.normSq_add, hnU, hnV, hD.1]
    norm_num
  have hmy : T.pairing (M 3) (V 3) = 1 / 2 := by
    rw [T.pairing_comm]
    change T.pairing (V 3) (T.add H (U 3) (V 3)) = _
    rw [T.pairing_add_right, hD.1, hnV]
    norm_num
  have hmx : T.pairing (M 3) (U 3) = 1 / 2 := by
    rw [T.pairing_comm]
    change T.pairing (U 3) (T.add H (U 3) (V 3)) = _
    rw [T.pairing_add_left, hD.1, hnU]
    norm_num
  have hmid : D.c = CATZero.mid h (D.y 3) (D.line 5) := by
    have hc := CATZero.mid_cn h (D.y 3) (D.line 5) D.c
    rw [D.radiusY, D.radiusLine] at hc
    apply dist_eq_zero.mp
    nlinarith [D.missing, dist_nonneg (x := D.c) (y := CATZero.mid h (D.y 3) (D.line 5))]
  have hop : T.Opposite (V 3) (L 5) := by
    have he := TangentCone.opposite_mid_logs h (D.y 3) (D.line 5)
    rw [← hmid] at he
    exact he
  have hsC := D.square 2 5 1 (by decide) (by decide) (by decide)
  have hcj : dist D.c (CATZero.mid h (D.x 2) (D.y 2)) ^ 2 = 1 / 4 := by
    rw [hsC.mid_eq h]
    exact D.lineFlat 5 1 (by decide)
  have hkj : dist (D.line 5) (CATZero.mid h (D.x 2) (D.y 2)) ^ 2 = 1 / 2 := by
    rw [hsC.mid_eq h, CATZero.dist_left_mid, div_pow, D.lineDist 5 1 (by decide)]
    norm_num
  have hex : L 5 = T.add H (M 2) (U 3) :=
    TangentCone.exceptional_identity h D.c (D.x 2) (D.y 2) (D.x 3) (D.line 5)
      (D.radiusX 2) (D.radiusY 2) (D.radiusX 3) (D.radiusLine 5)
      hsC.diagonal₀ D.twoStepX D.twoStepY hcj hkj D.loose D.fractional
  have hopex : T.Opposite (M 2) (M 3) :=
    T.exceptional_antipodes H hnM₂ hnM₃ hmy hmx hop hex
  apply T.five_line_fans_contradiction H (fun i : Fin 5 => L i.castSucc)
  · intro i
    exact hnL i.castSucc
  · intro i j hij
    exact hpL i.castSucc j.castSucc (fun he => hij (Fin.ext (congrArg (fun k : Fin 6 => k.val) he)))
  · exact hA₁.2.symm.trans hA₂.2
  · exact hB₁.2.symm.trans hB₂.2
  · change T.Opposite (T.add H (L 1) (L 3)) (T.add H (L 2) (L 4))
    rw [← hC.2, ← hD.2]
    exact hopex

end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
open Filter Topology
variable {X : Type*} [MetricSpace X]

/-- The elementary endpoint estimate behind first variation: fixing one
radial endpoint changes a comparison product by at most a first-order error.
It follows from the triangle inequality and convexity of the real square. -/
theorem radialPairing_endpoint_gap (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    2 * b * (radialPairing h o x y a b - radialPairing h o x y a 1) ≤
      a * dist o x ^ 2 := by
  let u := dist (segment h o x a) (segment h o y b)
  let v := dist (segment h o x a) y
  have htri : v ≤ u + (1 - b) * dist o y := by
    have he := dist_triangle (segment h o x a) (segment h o y b) y
    rw [segment_right h o y ⟨hb.1.le, hb.2⟩] at he
    exact he
  have huv : v ^ 2 ≤ (u + (1 - b) * dist o y) ^ 2 := by
    have hv : 0 ≤ v := dist_nonneg
    have hu : 0 ≤ u := dist_nonneg
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (dist_nonneg (x := o) (y := y))]
  have hs : b * v ^ 2 ≤ u ^ 2 + b * (1 - b) * dist o y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left huv hb.1.le,
      mul_nonneg (sub_nonneg.mpr hb.2) (sq_nonneg (u - b * dist o y))]
  have he₁ : 2 * a * radialPairing h o x y a 1 =
      a ^ 2 * dist o x ^ 2 + dist o y ^ 2 - v ^ 2 := by
    dsimp [radialPairing, v]
    rw [(segment_spec h o y).2.1]
    field_simp [ha.1.ne', hb.1.ne']
  have he₂ : 2 * a * b * radialPairing h o x y a b =
      a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 - u ^ 2 := by
    dsimp [radialPairing, u]
    field_simp [ha.1.ne', hb.1.ne']
  apply (mul_le_mul_iff_of_pos_left ha.1).mp
  have he₁' := congrArg (fun z : ℝ => b * z) he₁
  nlinarith [mul_nonneg hb.1.le (mul_nonneg (sq_nonneg a) (sq_nonneg (dist o x)))]

/-- First-variation comparison product along a quadratic radial parameter.
This suffices for the minimizer argument and avoids any assumed angle theorem. -/
theorem radialPairing_endpoint_tendsto (h : CATZero X) (o x y : X) :
    Tendsto (fun t : ℝ => radialPairing h o x y (t ^ 2) 1) (𝓝[>] 0)
      (𝓝 (tangentPairing h o x y)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hlim := radialPairing_tendsto h o x y (by simpa using ht.pow 2) ht
    (htp.mono fun _ hh => sq_pos_of_pos hh) htp
  have hlo : Tendsto (fun t : ℝ => radialPairing h o x y (t ^ 2) t -
      t * dist o x ^ 2 / 2) (𝓝[>] 0) (𝓝 (tangentPairing h o x y)) := by
    simpa using hlim.sub ((ht.mul_const (dist o x ^ 2)).div_const 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht0 ht1
    have hts : t ^ 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨sq_pos_of_pos ht0, by nlinarith⟩
    have he := radialPairing_endpoint_gap h o x y hts ⟨ht0, ht1⟩
    apply (mul_le_mul_iff_of_pos_left ht0).mp
    nlinarith
  · filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht0 ht1
    exact radialPairing_le_tangentPairing h o x y ⟨sq_pos_of_pos ht0, by nlinarith⟩
      (by norm_num)

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
open Filter Topology
variable {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]

/-- A finite squared-distance minimizer has nonpositive directional product
sum. The proof uses the actual comparison-product limit, not first variation
as an imported hypothesis. -/
theorem tangentPairing_sum_nonpos_of_minimum (h : CATZero X) (o : X) (y : ι → X)
    (hmin : ∀ x : X, (∑ i, dist o (y i) ^ 2) ≤ ∑ i, dist x (y i) ^ 2) (z : X) :
    (∑ i, tangentPairing h o z (y i)) ≤ 0 := by
  have hbound (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1) :
      (∑ i, radialPairing h o z (y i) a 1) ≤
        a * (Fintype.card ι : ℝ) * dist o z ^ 2 / 2 := by
    have he (i : ι) : dist (segment h o z a) (y i) ^ 2 =
        a ^ 2 * dist o z ^ 2 + dist o (y i) ^ 2 -
          2 * a * radialPairing h o z (y i) a 1 := by
      dsimp [radialPairing]
      rw [(segment_spec h o (y i)).2.1]
      field_simp [ha.1.ne']
      ring
    have hes := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => he i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hes
    have hm := hmin (segment h o z a)
    apply (mul_le_mul_iff_of_pos_left ha.1).mp
    nlinarith
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hlim := tendsto_finsetSum Finset.univ
    (fun i _ => radialPairing_endpoint_tendsto h o z (y i))
  have hr : Tendsto (fun t : ℝ => t ^ 2 * (Fintype.card ι : ℝ) * dist o z ^ 2 / 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (((ht.pow 2).mul_const (Fintype.card ι : ℝ)).mul_const
      (dist o z ^ 2)).div_const 2
  apply le_of_tendsto_of_tendsto hlim hr
  filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t ht0 ht1
  exact hbound (t ^ 2) ⟨sq_pos_of_pos ht0, by nlinarith⟩

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace TangentCone
open UniformSpace
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

theorem pairing_ray_log (p : TangentRay h o) (y : X) :
    (coneData h o).pairing (p : TangentCone h o) (log h o y) =
      (p.weight : ℝ) * CATZero.tangentPairing h o p.point y := by
  unfold ConeData.pairing ConeData.normSq
  change (dist (vertex h o) (p : TangentCone h o) ^ 2 +
    dist (vertex h o) (log h o y) ^ 2 - dist (p : TangentCone h o) (log h o y) ^ 2) / 2 = _
  rw [dist_vertex_log, vertex, log, Completion.dist_eq, Completion.dist_eq,
    TangentRay.dist_vertex, TangentRay.dist_sq]
  dsimp only [TangentRay.log, NNReal.coe_one]
  ring

/-- The tangent barycenter inequality at an actual finite squared-distance
minimizer, extended to the completed cone by density. -/
theorem pairing_sum_nonpos_of_minimum {ι : Type*} [Fintype ι] (y : ι → X)
    (hmin : ∀ x : X, (∑ i, dist o (y i) ^ 2) ≤ ∑ i, dist x (y i) ^ 2)
    (v : TangentCone h o) : (∑ i, (coneData h o).pairing v (log h o (y i))) ≤ 0 := by
  induction v using Completion.induction_on with
  | hp =>
    apply isClosed_le _ continuous_const
    unfold ConeData.pairing ConeData.normSq
    fun_prop
  | ih p =>
    simp_rw [pairing_ray_log]
    rw [← Finset.mul_sum]
    exact mul_nonpos_of_nonneg_of_nonpos p.weight.coe_nonneg
      (CATZero.tangentPairing_sum_nonpos_of_minimum h o y hmin p.point)

/-- Variance form of the zero tangent barycenter. -/
theorem variance_of_minimum {ι : Type*} [Fintype ι] (y : ι → X)
    (hmin : ∀ x : X, (∑ i, dist o (y i) ^ 2) ≤ ∑ i, dist x (y i) ^ 2)
    (v : TangentCone h o) :
    (Fintype.card ι : ℝ) * (coneData h o).normSq v + (∑ i, dist o (y i) ^ 2) ≤
      ∑ i, dist v (log h o (y i)) ^ 2 := by
  have hs := pairing_sum_nonpos_of_minimum h o y hmin v
  simp_rw [(coneData h o).dist_sq, normSq_log]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  linarith

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
end
end
end
end
end

end OAI
