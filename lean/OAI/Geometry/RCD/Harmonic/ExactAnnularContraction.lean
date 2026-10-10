import OAI.Geometry.RCD.Harmonic.RadialVolumeProfile

namespace OAI

/-! # Exact annular contraction after shrinking the initial center ball -/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem FullCD.closed_annular_contraction
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K < 0) (p : X) {r R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (ht1 : t < 1) :
    tau K n t R ^ n * μ (ball p R \ closedBall p r) ≤
      μ (closedBall p (t * R) \ ball p (t * r)) := by
  let δ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hδ (i : ℕ) : 0 < δ i := by dsimp only [δ]; positivity
  have hδzero : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδanti : Antitone δ := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity : 0 < (i : ℝ) + 1)
    exact_mod_cast Nat.add_le_add_right hij 1
  let A := ball p R \ closedBall p r
  let B : ℕ → Set X := fun i =>
    ball p (t * R + (1 + t) * δ i) \ closedBall p (t * r - (1 - t) * δ i)
  have hBmeas (i : ℕ) : MeasurableSet (B i) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hBanti : Antitone B := by
    intro i j hij x hx
    have hh := hδanti hij
    change dist x p < t * R + (1 + t) * δ j ∧
      ¬dist x p ≤ t * r - (1 - t) * δ j at hx
    change dist x p < t * R + (1 + t) * δ i ∧
      ¬dist x p ≤ t * r - (1 - t) * δ i
    constructor <;> nlinarith only [hx.1, hx.2, hh, ht, ht1]
  have hupper : Tendsto (fun i => t * R + (1 + t) * δ i) atTop (𝓝 (t * R)) := by
    simpa only [mul_zero, add_zero] using (hδzero.const_mul (1 + t)).const_add (t * R)
  have hlower : Tendsto (fun i => t * r - (1 - t) * δ i) atTop (𝓝 (t * r)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hδzero.const_mul (1 - t))
  have hBi : (⋂ i, B i) = closedBall p (t * R) \ ball p (t * r) := by
    ext x
    simp only [mem_iInter, Set.mem_sdiff, mem_ball, mem_closedBall]
    constructor
    · intro hx
      have hu : dist x p ≤ t * R :=
        ge_of_tendsto hupper (Eventually.of_forall fun i => (hx i).1.le)
      have hl : t * r ≤ dist x p :=
        le_of_tendsto hlower (Eventually.of_forall fun i => (lt_of_not_ge (hx i).2).le)
      exact ⟨hu, not_lt_of_ge hl⟩
    · rintro ⟨hu, hl⟩ i
      have hl' := le_of_not_gt hl
      have hd := hδ i
      have hp : 0 < (1 + t) * δ i := mul_pos (by linarith) hd
      have hm : 0 < (1 - t) * δ i := mul_pos (sub_pos.mpr ht1) hd
      change dist x p < t * R + (1 + t) * δ i ∧
        ¬dist x p ≤ t * r - (1 - t) * δ i
      constructor <;> linarith only [hu, hl', hp, hm]
  have hBfin : μ (B 0) ≠ ∞ := (hfin _ (isBounded_ball.subset sdiff_subset)).ne
  have hlimB := tendsto_measure_iInter_atTop (fun i => (hBmeas i).nullMeasurableSet)
    hBanti ⟨0, hBfin⟩
  rw [hBi] at hlimB
  have hmap : Tendsto (fun i => (t, R + δ i)) atTop (𝓝 (t, R)) := by
    exact tendsto_const_nhds.prodMk_nhds (by
      simpa only [add_zero] using hδzero.const_add R)
  have hc := (continuousAt_tau_nat_power_of_neg hK hn ht ht1 hR).tendsto.comp hmap
  have hAfin : μ A ≠ ∞ := (hfin _ (isBounded_ball.subset sdiff_subset)).ne
  have hcM := (ENNReal.continuous_mul_const hAfin).continuousAt.tendsto.comp hc
  apply le_of_tendsto_of_tendsto hcM hlimB
  exact Eventually.of_forall fun i =>
    hcd.annular_contraction μ hpos hfin hn hK.le p hR (hδ i) ht ht1

variable [ProperSpace X]

theorem NoncollapsedRCD.exact_annular_contraction {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K < 0) (p : X)
    {r R t : ℝ} (hr : 0 < r) (hrR : r < R) (ht : 0 < t) (ht1 : t < 1) :
    tau K n t R ^ n * (hausdorff n X) (ball p R \ closedBall p r) ≤
      (hausdorff n X) (ball p (t * R) \ closedBall p (t * r)) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  have hR : 0 < R := hr.trans hrR
  have htr : t * r < t * R := mul_lt_mul_of_pos_left hrR ht
  have h := hX.cd.closed_annular_contraction (hausdorff n X) hX.fullSupport
    hX.finiteOnBounded hn hK p hR ht ht1 (r := r)
  have hout := hX.closedBall_measure_eq_ball hn p (mul_pos ht hR)
  have hin := hX.closedBall_measure_eq_ball hn p (mul_pos ht hr)
  have heq : (hausdorff n X) (closedBall p (t * R) \ ball p (t * r)) =
      (hausdorff n X) (ball p (t * R) \ closedBall p (t * r)) := by
    rw [measure_sdiff ((ball_subset_ball htr.le).trans ball_subset_closedBall)
      measurableSet_ball.nullMeasurableSet (hX.finiteOnBounded _ isBounded_ball).ne,
      measure_sdiff (closedBall_subset_ball htr) measurableSet_closedBall.nullMeasurableSet
        (hX.finiteOnBounded _ isBounded_closedBall).ne, hout, hin]
  exact h.trans_eq heq

end RegularPointCoordinates

end OAI
