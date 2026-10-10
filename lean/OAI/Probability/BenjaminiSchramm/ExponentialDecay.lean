import OAI.Probability.BenjaminiSchramm.EventMeasurability
import OAI.Probability.UnimodularPercolation.Deformation.ClusterProducts
import OAI.Probability.UnimodularPercolation.Escape.CollisionTails

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem walk_crosses_sphere (H : SimpleGraph V) {x y : V} (w : H.Walk x y)
    (o : V) (n : ℕ) (hlo : H.dist o x ≤ n) (hhi : n ≤ H.dist o y) :
    ∃ z ∈ w.support, H.dist o z = n := by
  induction w with
  | @nil a => exact ⟨a, by simp, by omega⟩
  | @cons x a y ha w ih =>
    by_cases hx : H.dist o x = n
    · exact ⟨x, by simp, hx⟩
    · have had : H.dist o a ≤ n := by
        have hh := ha.diff_dist_adj (u := o)
        omega
      obtain ⟨z, hz, hd⟩ := ih had hhi
      exact ⟨z, by simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using Or.inr hz, hd⟩

theorem mem_reachBall_of_graphDistance_le (G : BondGraph V E) (hconn : Connected G)
    (x z : V) (m : ℕ) (hd : graphDistance G x z ≤ m) : z ∈ reachBall G x m := by
  obtain ⟨w, hw⟩ := ((conn_iff_reachable G Set.univ x z).mp
    (conn_univ_of_connected G hconn x z)).exists_walk_length_eq_dist
  obtain ⟨l, hl, he, _⟩ := walk_lift_bonds G Set.univ w
  have hlen : l.length = w.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map, SimpleGraph.Walk.length_edges] using hh
  exact reachBall_mono G x (hlen.trans_le (hw.trans_le hd)) hl.mem_reachBall

theorem sphere_split_subset (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (x y : V) (m r : ℕ) (hrm : r ≤ m)
    (hry : r ≤ graphDistance G x y) :
    {ω | Conn G ω x y} ⊆
      ⋃ z ∈ ((finite_reachBall hloc x m).toFinset.filter
        fun z => graphDistance G x z = r),
        DisjointOccurrence {ω | Conn G ω x z} {ω | Conn G ω z y} := by
  intro ω hc
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hc
  let q := w.bypass
  have hle : openSimpleGraph G ω ≤ openSimpleGraph G Set.univ := by
    rintro a b ⟨hne, e, _, he⟩
    exact ⟨hne, e, Set.mem_univ _, he⟩
  obtain ⟨z, hz, hzr⟩ := walk_crosses_sphere (openSimpleGraph G Set.univ)
    (q.mapLe hle) x r (by simp) hry
  have hzq : z ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz
  have hzB : z ∈ (finite_reachBall hloc x m).toFinset := by
    apply (finite_reachBall hloc x m).mem_toFinset.mpr
    exact mem_reachBall_of_graphDistance_le G hconn x z m (hzr.trans_le hrm)
  exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨hzB, hzr⟩, simplePath_disjoint_at G ω q w.bypass_isPath hzq⟩⟩

theorem twoPoint_le_sphere_sum [Countable E] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (p : unitInterval)
    (x y : V) (m r : ℕ) (hrm : r ≤ m) (hry : r ≤ graphDistance G x y) :
    twoPoint G p x y ≤
      ∑ z ∈ (finite_reachBall hloc x m).toFinset with graphDistance G x z = r,
        twoPoint G p x z * twoPoint G p z y := by
  let F := (finite_reachBall hloc x m).toFinset.filter fun z => graphDistance G x z = r
  calc
    _ ≤ (law p).real (⋃ z ∈ F,
        DisjointOccurrence {ω | Conn G ω x z} {ω | Conn G ω z y}) :=
      measureReal_mono (sphere_split_subset G hconn hloc x y m r hrm hry) (measure_ne_top _ _)
    _ ≤ ∑ z ∈ F, (law p).real
        (DisjointOccurrence {ω | Conn G ω x z} {ω | Conn G ω z y}) :=
      measureReal_biUnion_finset_le F _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      exact bk p _ _ (fun _ _ h hc => conn_mono G h hc)
        (fun _ _ h hc => conn_mono G h hc)
        (finiteWitness_conn G x z) (finiteWitness_conn G z y)

theorem connectivity_power_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (m k : ℕ) (x y : V) (hd : k * m ≤ graphDistance G x y) :
    ((m + 1 : ℕ) : ℝ) ^ k * twoPoint G p x y ≤
      (matrixCoeff (A ^ (k + 1)) x y).re := by
  have hk (a b : V) : matrixCoeff A a b = (twoPoint G p a b : ℂ) := hA a b
  have hpos : PositiveRealMatrix A := by
    intro a b
    rw [hk]
    exact ⟨rfl, twoPoint_nonneg G p a b⟩
  induction k generalizing x y with
  | zero => simp only [pow_zero, one_mul, zero_add, pow_one, hk, Complex.ofReal_re, le_refl]
  | succ k ih =>
    rw [Nat.succ_mul] at hd
    let B := (finite_reachBall hloc x m).toFinset
    let F (z : V) := twoPoint G p x z * (matrixCoeff (A ^ (k + 1)) z y).re
    have hF (z : V) : 0 ≤ F z :=
      mul_nonneg (twoPoint_nonneg G p x z) ((hpos.pow (k + 1)) z y).2
    have hsphere (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
        ((m + 1 : ℕ) : ℝ) ^ k * twoPoint G p x y ≤
          ∑ z ∈ B with graphDistance G x z = r, F z := by
      have hrm : r ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
      calc
        _ ≤ ((m + 1 : ℕ) : ℝ) ^ k *
            ∑ z ∈ B with graphDistance G x z = r,
              twoPoint G p x z * twoPoint G p z y :=
          mul_le_mul_of_nonneg_left (twoPoint_le_sphere_sum G hconn hloc p x y m r
            hrm (by omega)) (by positivity)
        _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro z hz
          have hxz := (Finset.mem_filter.mp hz).2
          have hzy : k * m ≤ graphDistance G z y := by
            have ht := ((conn_iff_reachable G Set.univ x z).mp
              (conn_univ_of_connected G hconn x z)).dist_triangle_left y
            change graphDistance G x y ≤ graphDistance G x z + graphDistance G z y at ht
            omega
          simpa only [F, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left (ih z y hzy) (twoPoint_nonneg G p x z)
    have havg := Finset.sum_le_sum hsphere
    have hfiber : (∑ r ∈ Finset.range (m + 1),
        ∑ z ∈ B with graphDistance G x z = r, F z) = ∑ z ∈ B, F z := by
      apply Finset.sum_fiberwise_of_maps_to
      intro z hz
      apply Finset.mem_range.mpr
      have hh := dist_le_of_mem_reachBall G x z m ((finite_reachBall hloc x m).mem_toFinset.mp hz)
      change graphDistance G x z ≤ m at hh
      omega
    rw [hfiber] at havg
    have hs := hpos.mul_hasSum (A ^ (k + 1)) x y
    simp only [hk, Complex.ofReal_re] at hs
    calc
      _ = ∑ _r ∈ Finset.range (m + 1),
          ((m + 1 : ℕ) : ℝ) ^ k * twoPoint G p x y := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
        ring
      _ ≤ ∑ z ∈ B, F z := havg
      _ ≤ ∑' z, F z := hs.summable.sum_le_tsum B (fun z _ => hF z)
      _ = (matrixCoeff (A ^ (k + 1 + 1)) x y).re := by
        rw [hs.tsum_eq]
        exact congrArg (fun T => (matrixCoeff T x y).re) (pow_succ' A (k + 1)).symm

theorem connectivity_block_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (m k : ℕ) (x y : V) (hd : k * m ≤ graphDistance G x y) :
    twoPoint G p x y ≤ ‖A‖ * (‖A‖ / (m + 1 : ℕ)) ^ k := by
  have hp := connectivity_power_lower G hconn hloc p A hA m k x y hd
  have hcoeff : (matrixCoeff (A ^ (k + 1)) x y).re ≤ ‖A‖ ^ (k + 1) := by
    apply (Complex.re_le_norm _).trans
    have hc : ‖matrixCoeff (A ^ (k + 1)) x y‖ ≤ ‖A ^ (k + 1)‖ := by
      change ‖(A ^ (k + 1)) (lp.single 2 y (1 : ℂ)) x‖ ≤ _
      apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        ((A ^ (k + 1)) (lp.single 2 y (1 : ℂ))) x).trans
      simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one, mul_one] using
        (A ^ (k + 1)).le_opNorm (lp.single 2 y (1 : ℂ))
    exact hc.trans (norm_pow_le' A (Nat.zero_lt_succ k))
  have hc : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    _ ≤ ‖A‖ ^ (k + 1) / ((m + 1 : ℕ) : ℝ) ^ k :=
      (le_div_iff₀ (pow_pos hc k)).mpr (by simpa only [mul_comm] using hp.trans hcoeff)
    _ = _ := by rw [div_pow, pow_succ]; ring

theorem connectivity_exponential_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (x y : V) :
    twoPoint G p x y ≤ 2 * ‖A‖ *
      Real.exp (-(Real.log 2 / (3 * ‖A‖)) * graphDistance G x y) := by
  have hM : 1 ≤ ‖A‖ := hA.norm_one_le G p A
  have hMp : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hM
  let m : ℕ := ⌈2 * ‖A‖⌉₊
  have hml : 2 * ‖A‖ ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) ≤ 3 * ‖A‖ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * ‖A‖ by positivity)
    dsimp [m]
    linarith
  have hmp : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hml
    exact_mod_cast this
  let k := graphDistance G x y / m
  have hk : k * m ≤ graphDistance G x y := Nat.div_mul_le_self _ _
  have hxy : graphDistance G x y < (k + 1) * m := by
    simpa only [k, Nat.mul_comm] using Nat.lt_mul_div_succ (graphDistance G x y) hmp
  have hr : ‖A‖ / (m + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
    push_cast
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖A‖ / (m + 1 : ℕ)) hr k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (graphDistance G x y : ℝ) ≤ ((k : ℝ) + 1) * (3 * ‖A‖) := by
    have h1 : (graphDistance G x y : ℝ) ≤ ((k : ℝ) + 1) * m := by
      exact_mod_cast hxy.le
    exact h1.trans (mul_le_mul_of_nonneg_left hmu (by positivity))
  have hexponent : -(Real.log 2) * k ≤
      Real.log 2 - (Real.log 2 / (3 * ‖A‖)) * graphDistance G x y := by
    have hdiv : (graphDistance G x y : ℝ) / (3 * ‖A‖) ≤ (k : ℝ) + 1 :=
      (div_le_iff₀ (by positivity)).mpr hcast
    have hh := mul_le_mul_of_nonneg_left hdiv hlog.le
    nlinarith [show (Real.log 2 / (3 * ‖A‖)) * graphDistance G x y =
      Real.log 2 * ((graphDistance G x y : ℝ) / (3 * ‖A‖)) by ring]
  have hhalf : (1 / 2 : ℝ) ^ k = Real.exp (-(Real.log 2) * k) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  calc
    _ ≤ ‖A‖ * (‖A‖ / (m + 1 : ℕ)) ^ k :=
      connectivity_block_bound G hconn hloc p A hA m k x y hk
    _ ≤ ‖A‖ * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖A‖ * Real.exp (-(Real.log 2) * k) := by rw [hhalf]
    _ ≤ ‖A‖ * Real.exp (Real.log 2 -
        (Real.log 2 / (3 * ‖A‖)) * graphDistance G x y) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (norm_nonneg _)
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        neg_mul, Real.exp_neg, div_eq_mul_inv]
      ring

theorem exponentialDecay_of_bounded [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (hb : OperatorBounded G p) : ExponentialDecay G p := by
  obtain ⟨A, hA⟩ := hb
  have hM : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one (hA.norm_one_le G p A)
  exact ⟨2 * ‖A‖, Real.log 2 / (3 * ‖A‖), by positivity,
    div_pos (Real.log_pos (by norm_num)) (by positivity),
    connectivity_exponential_bound G hconn hloc p A hA⟩

theorem exponentialDecay_of_lt_ptwo [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (hp : p < ptwo G) : ExponentialDecay G p := by
  obtain ⟨q, hq, hpq⟩ := lt_sSup_iff.mp hp
  exact exponentialDecay_of_bounded G hconn hloc p
    (operatorBounded_of_le G hpq.le hq)

theorem ptwo_le_pexp [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) :
    ptwo G ≤ pexp G := by
  apply le_of_forall_lt_imp_le_of_dense
  intro p hp
  exact le_sSup (exponentialDecay_of_lt_ptwo G hconn hloc p hp)

end Percolation.BenjaminiSchramm

end OAI
