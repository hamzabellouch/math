import OAI.Geometry.RCD.Metric.CountableTimeCompactness
import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential
import OAI.Geometry.RCD.Heat.ScaledCompactSpacetimeBound

namespace OAI

/-! # Simultaneous compactness on a countable family of heat cylinders

The reference time and center are the same on every cylinder. This makes
the limiting functions agree on their common domains outside one common
countable exceptional time set.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_countable_regions (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (r δ : ℕ → ℝ) (hr : ∀ m, 0 ≤ r m) (hδ : ∀ m, 0 < δ m) (hδ1 : ∀ m, δ m ≤ 1) :
    ∃ (L : ℕ → ℝ≥0) (M : ℕ → ℝ) (g : ∀ m, ℝ → closedBall z (r m) → ℝ)
      (a : ℕ → ℕ) (N : Set ℝ),
      StrictMono a ∧ N.Countable ∧
      (∀ m, (∀ t x, |g m t x| ≤ M m) ∧ (∀ t, LipschitzWith (L m) (g m t)) ∧
        (∀ x, Monotone (fun t => g m t x)) ∧
        ∀ t ∈ Ioo (δ m) 1, t ∉ N → TendstoUniformly
          (fun k (x : closedBall z (r m)) =>
            hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k))
              (δ m) (hδ m) z t x) (g m t) atTop) ∧
      ∀ i j t, t ∈ Ioo (δ i) 1 → t ∈ Ioo (δ j) 1 → t ∉ N →
        ∀ x (hi : x ∈ closedBall z (r i)) (hj : x ∈ closedBall z (r j)),
          g i t ⟨x,hi⟩ = g j t ⟨x,hj⟩ := by
  classical
  let Y := fun m => closedBall z (r m)
  let (m : ℕ) : CompactSpace (Y m) := isCompact_iff_compactSpace.mp (isCompact_closedBall z (r m))
  let (m : ℕ) : Nonempty (Y m) := ⟨⟨z,mem_closedBall_self (hr m)⟩⟩
  obtain ⟨C,D,_hC,_hD,hLip⟩ := hX.compact_heat_factor_scaled_lipschitz hn p
  let L := fun m => (⟨Real.sqrt (Real.exp |K| *
    (4*C/(δ m)+16*D*(R+8*(r m+1))^2/(δ m)^2)),Real.sqrt_nonneg _⟩ : ℝ≥0)
  choose M hM hbound using fun m => hX.scaled_compact_heat_spacetime_bounded hn p hK
    ν ρ hρ hρ0 hB hν z R hR hdist (hδ m) (hr m)
  let f := fun m k t (x : Y m) => hX.fixedGaugeScaledPotential hn p ν (F k)
    (ε k) (hε k) (δ m) (hδ m) z t x
  have hb (m k : ℕ) (t : ℝ) (ht : t ∈ Icc (δ m) 1) (x : Y m) : |f m k t x| ≤ M m := by
    dsimp only [f]
    rw [hX.fixedGaugeScaledPotential_eq hn p ν (F k) (ε k) (hε k) (δ m) (hδ m) z ht.1 x]
    exact hbound m (F k) (hF k) (hε k) (hε1 k) ht.1 ht.2 x x.property
  have hl (m k : ℕ) (t : ℝ) (ht : t ∈ Icc (δ m) 1) : LipschitzWith (L m) (f m k t) := by
    have hloc : LipschitzOnWith (L m)
        (hX.scaledCompactHeatPotential hn p ν (F k) (ε k) t
          (div_pos (mul_pos (hε k) ((hδ m).trans_le ht.1)) (by norm_num))) (ball z (r m+1)) :=
      hLip ν ρ hρ hρ0 hB hν (F k) (hF k) (hε k) (hε1 k) (hδ m) ht.1 ht.2
        z R hR hdist (by linarith [hr m])
    have hres : LipschitzWith (L m) (fun x : Y m =>
        hX.scaledCompactHeatPotential hn p ν (F k) (ε k) t
          (div_pos (mul_pos (hε k) ((hδ m).trans_le ht.1)) (by norm_num)) x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact hloc.dist_le_mul x (mem_ball.mpr (by linarith [mem_closedBall.mp x.property]))
        y (mem_ball.mpr (by linarith [mem_closedBall.mp y.property]))
    have heq : f m k t = fun x : Y m =>
        hX.scaledCompactHeatPotential hn p ν (F k) (ε k) t
          (div_pos (mul_pos (hε k) ((hδ m).trans_le ht.1)) (by norm_num)) x -
        ε k * Real.log (hX.compactHeatFactor hn p ν (F k) (ε k) (hε k) z) :=
      funext fun x => hX.fixedGaugeScaledPotential_eq hn p ν (F k) (ε k) (hε k) (δ m) (hδ m) z ht.1 x
    rw [heq]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hres.dist_le_mul x y
  let e := fun m k => ε k*((n:ℝ)/(δ m)+(n:ℝ)*|K|/2)
  have he (m : ℕ) : Tendsto (e m) atTop (𝓝 0) := by
    have hh := hε0.mul_const ((n:ℝ)/(δ m)+(n:ℝ)*|K|/2)
    simp only [zero_mul] at hh
    exact hh
  have ho (m k : ℕ) (s t : ℝ) (hs : δ m ≤ s) (hst : s ≤ t) (_ht : t ≤ 1) (x : Y m) :
      f m k s x-f m k t x ≤ e m k*(t-s) := by
    dsimp only [f]
    rw [hX.fixedGaugeScaledPotential_eq hn p ν (F k) (ε k) (hε k) (δ m) (hδ m) z hs x,
      hX.fixedGaugeScaledPotential_eq hn p ν (F k) (ε k) (hε k) (δ m) (hδ m) z (hs.trans hst) x]
    have hh := hX.scaled_compact_heat_potential_interior_time_lower hn p hK
      ν ρ hρ hρ0 hB hν (F k) (hF k) (hε k) (hε1 k) (hδ m) hs hst x
    dsimp only [e]
    linarith
  obtain ⟨g,a,N,ha,hN,hg⟩ := countable_almost_monotone_compactness δ M L hδ1 hM f e he hb hl ho
  refine ⟨L,M,g,a,N,ha,hN,hg,?_⟩
  intro i j t hi hj htN x hxi hxj
  have hli := ((hg i).2.2.2 t hi htN).tendsto_at ⟨x,hxi⟩
  have hlj := ((hg j).2.2.2 t hj htN).tendsto_at ⟨x,hxj⟩
  have heq (k : ℕ) : f i (a k) t ⟨x,hxi⟩ = f j (a k) t ⟨x,hxj⟩ := by
    simp only [f,fixedGaugeScaledPotential,max_eq_right hi.1.le,max_eq_right hj.1.le]
  exact tendsto_nhds_unique hli (hlj.congr' (Eventually.of_forall fun k => (heq k).symm))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
