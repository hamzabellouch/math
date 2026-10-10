import OAI.Dynamics.TriangleBilliards.RegularRays

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

open Filter
open scoped Topology

lemma crossMap_flight (p x v : ℂ) (t : ℝ) :
    crossMap v (x + t • v - p) = crossMap v (x - p) := by
  rw [show x + t • v - p = (x - p) + t • v by abel,
    map_add, map_smul, crossMap_self, smul_zero, add_zero]

lemma crossMap_abs_le (v : Circle) (x : ℂ) : |crossMap v x| ≤ ‖x‖ := by
  calc
    |crossMap v x| ≤ ‖x * star (v : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖x‖ := by rw [norm_mul, norm_star, Circle.norm_coe, mul_one]

lemma wallReflection_fixed_vertex (Q : Triangle) (i k : Fin 3) (hk : k ≠ i + 2) :
    wallReflection Q i (Q.vertex k) = Q.vertex k := by
  have h : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases h with rfl | rfl | h
  · simp [wallReflection, reflect]
  · change Q.vertex i + reflect (Q.tangent i) (Q.tangent i) = Q.vertex (i + 1)
    rw [reflect_tangent (Q.tangent_ne_zero i), Triangle.tangent]
    abel
  · exact False.elim (hk h)

namespace Admissible

lemma wall_ne_next {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate n).collision.wall ≠ (z.iterate (n + 1)).collision.wall := by
  intro he
  let i := (z.iterate n).collision.wall
  have h0 : Q.basis.coord (i + 2) (z.iterate (n + 1)).pos = 0 :=
    (Q.side_coord_zero_iff (z.iterate_on_side n) (i + 2)).mpr rfl
  have hp : 0 < Q.slope (i + 2) (z.iterate (n + 1)).vel :=
    (z.iterate (n + 1)).inward.2 (i + 2) h0
  have h1 : Q.basis.coord (i + 2) (z.iterate (n + 2)).pos = 0 := by
    apply (Q.side_coord_zero_iff (z.iterate_on_side (n + 1)) (i + 2)).mpr
    rw [← he]
  change Q.basis.coord (i + 2) ((z.iterate (n + 1)).pos +
    (z.iterate (n + 1)).collision.delay • ((z.iterate (n + 1)).vel : ℂ)) = 0 at h1
  rw [Q.coord_shift, h0, zero_add] at h1
  exact (ne_of_gt (mul_pos (z.iterate (n + 1)).collision.positive hp)) h1

lemma dist_iterate_le_dist_time {Q : Triangle} (z : Admissible Q) (m n : ℕ) :
    dist (z.iterate m).pos (z.iterate n).pos ≤ dist (z.time m) (z.time n) := by
  rcases le_total m n with h | h
  · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (z.time_strictMono.monotone h))]
    exact z.dist_iterate_le_time h
  · rw [dist_comm (z.iterate m).pos, dist_comm (z.time m), Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (z.time_strictMono.monotone h))]
    exact z.dist_iterate_le_time h

lemma positions_converge_of_bounded_time {Q : Triangle} (z : Admissible Q)
    (hb : BddAbove (range z.time)) :
    ∃ p : ℂ, Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p) := by
  have ht := tendsto_atTop_ciSup z.time_strictMono.monotone hb
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq ε hε
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt (z.dist_iterate_le_dist_time m n) (hN m hm n hn)⟩

/-- If infinitely many collisions accumulated in finite distance, their
common limit would have to be a vertex, not an arbitrary boundary point. -/
lemma limit_is_vertex {Q : Triangle} (z : Admissible Q) {p : ℂ}
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p)) : ∃ k, p = Q.vertex k := by
  have hc (i : Fin 3) : Tendsto (fun n => Q.basis.coord i (z.iterate n).pos) atTop
      (𝓝 (Q.basis.coord i p)) :=
    (Q.basis.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp hp
  have hnonneg (i : Fin 3) : 0 ≤ Q.basis.coord i p :=
    ge_of_tendsto' (hc i) (fun n => (z.iterate n).inward.1 i)
  have hz : ∃ i, Q.basis.coord i p = 0 := by
    by_contra hn
    push Not at hn
    have hpos (i : Fin 3) : 0 < Q.basis.coord i p := lt_of_le_of_ne (hnonneg i) (hn i).symm
    have he : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < Q.basis.coord i (z.iterate n).pos :=
      eventually_all.mpr fun i => (hc i).eventually (lt_mem_nhds (hpos i))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    have hzero := (Q.side_coord_zero_iff (z.iterate_on_side N)
      ((z.iterate N).collision.wall + 2)).mpr rfl
    have hpositive := hN (N + 1) (Nat.le_succ N) ((z.iterate N).collision.wall + 2)
    linarith
  by_contra hn
  push Not at hn
  obtain ⟨i, hi⟩ := Q.boundary_open_side hnonneg hz hn
  have hpos (j : Fin 3) (hj : j ≠ i + 2) : 0 < Q.basis.coord j p := by
    apply lt_of_le_of_ne (hnonneg j)
    intro hj0
    exact hj ((Q.side_coord_zero_iff hi j).mp hj0.symm)
  have he : ∀ᶠ n : ℕ in atTop, ∀ j, j ≠ i + 2 → 0 < Q.basis.coord j (z.iterate n).pos := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = i + 2
    · exact Eventually.of_forall fun _ h => False.elim (h hj)
    · exact ((hc j).eventually (lt_mem_nhds (hpos j hj))).mono fun _ h _ => h
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hw (n : ℕ) (hn : N ≤ n + 1) : (z.iterate n).collision.wall = i := by
    apply add_right_cancel (b := (2 : Fin 3))
    by_contra h
    have hz := (Q.side_coord_zero_iff (z.iterate_on_side n)
      ((z.iterate n).collision.wall + 2)).mpr rfl
    have hp := hN (n + 1) hn ((z.iterate n).collision.wall + 2) h
    linarith
  exact z.wall_ne_next N ((hw N (by omega)).trans (hw (N + 1) (by omega)).symm)

/-- Absolute angular momentum about a fixed point. -/
def momentum {Q : Triangle} (z : Admissible Q) (p : ℂ) : ℝ :=
  |crossMap z.vel (z.pos - p)|

lemma momentum_next {Q : Triangle} (z : Admissible Q) (p : ℂ)
    (hp : wallReflection Q z.collision.wall p = p) : z.next.momentum p = z.momentum p := by
  have hx := wallReflection_fixed_side Q z.collision.on_side
  have h := crossMap_reflect (Q.tangent_ne_zero z.collision.wall) (z.vel : ℂ)
    (z.pos + z.collision.delay • (z.vel : ℂ) - p)
  rw [← wallReflection_sub, hx, hp, crossMap_flight] at h
  change |crossMap (reflect (Q.tangent z.collision.wall) z.vel)
    (z.pos + z.collision.delay • (z.vel : ℂ) - p)| = |crossMap (z.vel : ℂ) (z.pos - p)|
  rw [h, abs_neg]

lemma momentum_tendsto_zero {Q : Triangle} (z : Admissible Q) {p : ℂ}
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p)) :
    Tendsto (fun n => (z.iterate n).momentum p) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖(z.iterate n).pos - p‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hp.sub_const p).norm
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => crossMap_abs_le _ _) hnorm

lemma eventually_wall_fixed_of_vertex_limit {Q : Triangle} (z : Admissible Q) (k : Fin 3)
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 (Q.vertex k))) :
    ∀ᶠ n : ℕ in atTop, wallReflection Q (z.iterate n).collision.wall (Q.vertex k) = Q.vertex k := by
  have hc := (Q.basis.coord k).continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (hp.comp (tendsto_add_atTop_nat 1))
  have hk : Q.basis.coord k (Q.vertex k) = 1 := Q.basis.coord_apply_eq k
  filter_upwards [hc.eventually (lt_mem_nhds (by rw [hk]; norm_num : 0 <
    Q.basis.coord k (Q.vertex k)))] with n hn
  apply wallReflection_fixed_vertex
  intro he
  have hz := (Q.side_coord_zero_iff (z.iterate_on_side n) k).mpr he
  change 0 < Q.basis.coord k (z.iterate (n + 1)).pos at hn
  linarith

/-- Non-Zeno is proved, not added as an admissibility hypothesis: finite
accumulation would approach a vertex, where conservation of absolute
angular momentum forces this regular ray to aim through that vertex. -/
lemma time_not_bddAbove {Q : Triangle} (z : Admissible Q) : ¬ BddAbove (range z.time) := by
  intro hb
  obtain ⟨p, hp⟩ := z.positions_converge_of_bounded_time hb
  obtain ⟨k, rfl⟩ := z.limit_is_vertex hp
  have he := z.eventually_wall_fixed_of_vertex_limit k hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hconst (n : ℕ) (hn : N ≤ n) :
      (z.iterate n).momentum (Q.vertex k) = (z.iterate N).momentum (Q.vertex k) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      exact ((z.iterate n).momentum_next (Q.vertex k) (hN n hn)).trans ih
  have ht : Tendsto (fun n => (z.iterate n).momentum (Q.vertex k)) atTop
      (𝓝 ((z.iterate N).momentum (Q.vertex k))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => (hconst n hn).symm⟩)
  have hm := tendsto_nhds_unique ht (z.momentum_tendsto_zero hp)
  apply (z.iterate N).regular
  simp only [vertexExceptional, mem_iUnion]
  refine ⟨[], k, ?_⟩
  exact abs_eq_zero.mp hm

lemma time_unbounded_above {Q : Triangle} (z : Admissible Q) (t : ℝ) :
    ∃ n : ℕ, t < z.time n := by
  by_contra hn
  push Not at hn
  apply z.time_not_bddAbove
  exact ⟨t, fun _ ⟨n, hn'⟩ => hn' ▸ hn n⟩

end Admissible

lemma reflect_neg (e v : ℂ) : reflect e (-v) = -reflect e v := by
  simp [reflect]

lemma vertexExceptional_neg_iff (Q : Triangle) (x : ℂ) (v : Circle) :
    (x, -v) ∈ vertexExceptional Q ↔ (x, v) ∈ vertexExceptional Q := by
  simp only [vertexExceptional, mem_iUnion, aimingAt, mem_ofPred_eq, Circle.coe_neg]
  have he (p : ℂ) : crossMap (-(v : ℂ)) (x - p) = -crossMap v (x - p) := by
    simp [crossMap]
  simp only [he, neg_eq_zero]

/-- The two genuine recursively generated rays, joined at an interior state. -/
structure TwoRays (Q : Triangle) (z : Phase) where
  interior_pos : z.1 ∈ Q.table
  forward : Admissible Q
  backward : Admissible Q
  forward_pos : forward.pos = z.1
  backward_pos : backward.pos = z.1
  forward_vel : forward.vel = z.2
  backward_vel : backward.vel = -z.2

noncomputable def regularRays (Q : Triangle) (z : Phase) (hx : z.1 ∈ Q.table)
    (hr : z ∉ vertexExceptional Q) : TwoRays Q z where
  interior_pos := hx
  forward := ⟨z.1, z.2, Q.inward_of_table hx, hr⟩
  backward := ⟨z.1, -z.2, Q.inward_of_table hx, by rwa [vertexExceptional_neg_iff]⟩
  forward_pos := rfl
  backward_pos := rfl
  forward_vel := rfl
  backward_vel := rfl

namespace TwoRays

variable {Q : Triangle} {z : Phase} (r : TwoRays Q z)

def time : ℤ → ℝ
  | .ofNat 0 => -r.backward.time 1
  | .ofNat (n + 1) => r.forward.time (n + 1)
  | .negSucc n => -r.backward.time (n + 2)

def point : ℤ → ℂ
  | .ofNat 0 => (r.backward.iterate 1).pos
  | .ofNat (n + 1) => (r.forward.iterate (n + 1)).pos
  | .negSucc n => (r.backward.iterate (n + 2)).pos

def direction : ℤ → Circle
  | .ofNat n => (r.forward.iterate n).vel
  | .negSucc n => -(r.backward.iterate (n + 1)).vel

def wall : ℤ → Fin 3
  | .ofNat 0 => r.backward.collision.wall
  | .ofNat (n + 1) => (r.forward.iterate n).collision.wall
  | .negSucc n => (r.backward.iterate (n + 1)).collision.wall

lemma zero_before : r.time 0 < 0 := by
  change -r.backward.time 1 < 0
  have h := r.backward.time_strictMono (Nat.zero_lt_succ 0)
  rw [r.backward.time_zero] at h
  exact neg_neg_of_pos h

lemma zero_after : 0 < r.time 1 := by
  change 0 < r.forward.time 1
  have h := r.forward.time_strictMono (Nat.zero_lt_succ 0)
  rwa [r.forward.time_zero] at h

lemma increasing : StrictMono r.time := by
  apply strictMono_int_of_lt_succ
  intro n
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact lt_trans r.zero_before r.zero_after
    | succ n => exact r.forward.time_strictMono (Nat.lt_succ_self (n + 1))
  | negSucc n =>
    cases n with
    | zero => exact neg_lt_neg (r.backward.time_strictMono (by omega : 1 < 2))
    | succ n => exact neg_lt_neg (r.backward.time_strictMono (Nat.lt_succ_self (n + 2)))

lemma unbounded_above (t : ℝ) : ∃ n : ℤ, t < r.time n := by
  obtain ⟨n, hn⟩ := r.forward.time_unbounded_above t
  exact ⟨Int.ofNat (n + 1), lt_trans hn (r.forward.time_strictMono (Nat.lt_succ_self n))⟩

lemma unbounded_below (t : ℝ) : ∃ n : ℤ, r.time n < t := by
  obtain ⟨n, hn⟩ := r.backward.time_unbounded_above (-t)
  refine ⟨Int.negSucc n, ?_⟩
  change -r.backward.time (n + 2) < t
  have h := r.backward.time_strictMono (by omega : n < n + 2)
  linarith

lemma on_side (n : ℤ) : r.point n ∈ Q.side (r.wall n) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact r.backward.iterate_on_side 0
    | succ n => exact r.forward.iterate_on_side n
  | negSucc n => exact r.backward.iterate_on_side (n + 1)

lemma middle_point :
    r.point 0 = z.1 - r.backward.time 1 • (z.2 : ℂ) := by
  change (r.backward.iterate 1).pos = _
  rw [r.backward.iterate_flight 0, r.backward.time_zero, sub_zero]
  change r.backward.pos + r.backward.time 1 • (r.backward.vel : ℂ) = _
  rw [r.backward_pos, r.backward_vel, Circle.coe_neg, smul_neg, sub_eq_add_neg]

lemma start_point : z.1 = r.point 0 + (-r.time 0) • (r.direction 0 : ℂ) := by
  rw [r.middle_point]
  change z.1 = z.1 - r.backward.time 1 • (z.2 : ℂ) +
    (- -r.backward.time 1) • (r.forward.vel : ℂ)
  rw [neg_neg, r.forward_vel]
  abel

lemma flight (n : ℤ) : r.point (n + 1) = r.point n +
    (r.time (n + 1) - r.time n) • (r.direction n : ℂ) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change r.point 1 = r.point 0 + (r.time 1 - r.time 0) • (r.direction 0 : ℂ)
      rw [r.middle_point]
      change (r.forward.iterate 1).pos = z.1 - r.backward.time 1 • (z.2 : ℂ) +
        (r.forward.time 1 - -r.backward.time 1) • (r.forward.vel : ℂ)
      rw [r.forward.iterate_flight 0, r.forward.time_zero, sub_zero]
      change r.forward.pos + r.forward.time 1 • (r.forward.vel : ℂ) = _
      rw [r.forward_pos, r.forward_vel, sub_neg_eq_add, add_smul]
      abel
    | succ n => exact r.forward.iterate_flight (n + 1)
  | negSucc n =>
    have h := r.backward.iterate_flight (n + 1)
    cases n with
    | zero =>
      change (r.backward.iterate 1).pos = (r.backward.iterate 2).pos +
        (-r.backward.time 1 - -r.backward.time 2) • (-(r.backward.iterate 1).vel : Circle)
      rw [Circle.coe_neg, smul_neg, h]
      rw [show -r.backward.time 1 - -r.backward.time 2 =
        r.backward.time 2 - r.backward.time 1 by ring]
      abel
    | succ n =>
      change (r.backward.iterate (n + 2)).pos = (r.backward.iterate (n + 3)).pos +
        (-r.backward.time (n + 2) - -r.backward.time (n + 3)) •
          (-(r.backward.iterate (n + 2)).vel : Circle)
      rw [Circle.coe_neg, smul_neg, h]
      rw [show -r.backward.time (n + 2) - -r.backward.time (n + 3) =
        r.backward.time (n + 3) - r.backward.time (n + 2) by ring]
      abel

lemma middle_flight (t : ℝ) :
    r.point 0 + (t - r.time 0) • (r.direction 0 : ℂ) = z.1 + t • (z.2 : ℂ) := by
  rw [r.middle_point]
  change z.1 - r.backward.time 1 • (z.2 : ℂ) +
    (t - -r.backward.time 1) • (r.forward.vel : ℂ) = _
  rw [r.forward_vel, sub_neg_eq_add, add_smul]
  abel

lemma inside (n : ℤ) (t : ℝ) (h0 : r.time n < t) (h1 : t < r.time (n + 1)) :
    r.point n + (t - r.time n) • (r.direction n : ℂ) ∈ Q.table := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change r.point 0 + (t - r.time 0) • (r.direction 0 : ℂ) ∈ Q.table
      rw [r.middle_flight]
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · have h : -t < r.backward.time 1 := by change -r.backward.time 1 < t at h0; linarith
        have hp := r.backward.iterate_inside 0 (t := -t)
          (by rw [r.backward.time_zero]; linarith) h
        change r.backward.pos + (-t - r.backward.time 0) • (r.backward.vel : ℂ) ∈ Q.table at hp
        simpa only [r.backward.time_zero, sub_zero, r.backward_pos, r.backward_vel,
          Circle.coe_neg, smul_neg, neg_smul, neg_neg] using hp
      · simpa only [zero_smul, add_zero] using r.interior_pos
      · have hp := r.forward.iterate_inside 0 (t := t)
          (by rw [r.forward.time_zero]; exact ht) h1
        change r.forward.pos + (t - r.forward.time 0) • (r.forward.vel : ℂ) ∈ Q.table at hp
        simpa only [r.forward.time_zero, sub_zero, r.forward_pos, r.forward_vel] using hp
    | succ n => exact r.forward.iterate_inside (n + 1) h0 h1
  | negSucc n =>
    have ht0 : r.backward.time (n + 1) < -t := by
      cases n with
      | zero => change t < -r.backward.time 1 at h1; linarith
      | succ n => change t < -r.backward.time (n + 2) at h1; linarith
    have ht1 : -t < r.backward.time (n + 2) := by
      change -r.backward.time (n + 2) < t at h0
      linarith
    have hp := r.backward.iterate_inside (n + 1) ht0 ht1
    change (r.backward.iterate (n + 2)).pos + (t - -r.backward.time (n + 2)) •
      (-(r.backward.iterate (n + 1)).vel : Circle) ∈ Q.table
    rw [Circle.coe_neg, smul_neg, r.backward.iterate_flight (n + 1)]
    convert hp using 1
    module

lemma specular (n : ℤ) :
    (r.direction n : ℂ) = reflect (Q.tangent (r.wall n)) (r.direction (n - 1) : ℂ) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change (r.forward.vel : ℂ) = reflect (Q.tangent r.backward.collision.wall)
        (-(r.backward.iterate 1).vel : Circle)
      change (r.forward.vel : ℂ) = reflect (Q.tangent r.backward.collision.wall)
        (-reflectedDirection Q r.backward.collision.wall r.backward.vel : Circle)
      rw [Circle.coe_neg, reflect_neg]
      change (r.forward.vel : ℂ) = -reflect (Q.tangent r.backward.collision.wall)
        (reflect (Q.tangent r.backward.collision.wall) r.backward.vel)
      rw [reflect_involutive (Q.tangent_ne_zero _), r.forward_vel, r.backward_vel,
        Circle.coe_neg, neg_neg]
    | succ n =>
      change ((r.forward.iterate n).next.vel : ℂ) = reflect
        (Q.tangent (r.forward.iterate n).collision.wall) (r.direction (Int.ofNat (n + 1) - 1) : ℂ)
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by change (↑(n + 1) : ℤ) - 1 = ↑n; omega]
      rfl
  | negSucc n =>
    change (-(r.backward.iterate (n + 1)).vel : Circle) = reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (r.direction (Int.negSucc n - 1) : ℂ)
    rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by omega]
    change (-(r.backward.iterate (n + 1)).vel : Circle) = reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (-reflectedDirection Q (r.backward.iterate (n + 1)).collision.wall
        (r.backward.iterate (n + 1)).vel : Circle)
    rw [Circle.coe_neg, Circle.coe_neg, reflect_neg]
    change -((r.backward.iterate (n + 1)).vel : ℂ) = -reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (reflect (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
        (r.backward.iterate (n + 1)).vel)
    rw [reflect_involutive (Q.tangent_ne_zero _)]

/-- The full two-sided, non-Zeno, specular chain, assembled from actual exits. -/
def chain : FlightChain Q z where
  time := r.time
  point := r.point
  direction := r.direction
  wall := r.wall
  increasing := r.increasing
  unbounded_below := r.unbounded_below
  unbounded_above := r.unbounded_above
  zero_before := r.zero_before
  zero_after := r.zero_after
  on_side := r.on_side
  flight := r.flight
  inside := r.inside
  start_point := r.start_point
  start_direction := r.forward_vel.symm
  specular := r.specular

end TwoRays

lemma exists_chain_of_not_exceptional (Q : Triangle) (z : Phase) (hx : z.1 ∈ Q.table)
    (hr : z ∉ vertexExceptional Q) : Nonempty (FlightChain Q z) :=
  ⟨(regularRays Q z hx hr).chain⟩

lemma ae_position_in_table (Q : Triangle) : ∀ᵐ z ∂phaseMeasure Q, z.1 ∈ Q.table := by
  rw [ae_iff]
  rw [show {a : Phase | a.1 ∉ Q.table} = Q.tableᶜ ×ˢ (univ : Set Circle) by
    ext a; simp]
  rw [phaseMeasure, Measure.prod_prod, Measure.smul_apply,
    Measure.restrict_apply Q.measurableSet_table.compl]
  simp only [compl_inter_self, measure_empty, smul_zero, zero_mul]

/-- Complete regular trajectories exist for almost every initial state under
exact normalized area-angular measure; all collisions and both infinite
ends have been constructed above, with no completeness hypothesis. -/
lemma ae_exists_chain (Q : Triangle) :
    ∀ᵐ z ∂phaseMeasure Q, Nonempty (FlightChain Q z) := by
  have hr : ∀ᵐ z ∂phaseMeasure Q, z ∉ vertexExceptional Q := by
    rw [ae_iff]
    convert phaseMeasure_vertexExceptional Q using 2
    ext a; simp
  filter_upwards [ae_position_in_table Q, hr] with z hx hz
  exact exists_chain_of_not_exceptional Q z hx hz

end TriangularBilliards
end

end OAI
