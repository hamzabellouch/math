import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPicardContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightedLocal

namespace OAI

/-! # Continuity of bounded actual mild-solution families

The local polynomial Lipschitz estimate is used only along the actual two
solutions.  Exponential weighting gives a uniform pair contraction, so
continuity follows from continuity of the Picard map at a fixed path.  No
globally Lipschitz extension of the reaction is introduced.
-/

open Set Filter Topology

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep expandingDuhamel expandingPicard
  expandingBieleckiPicard expandingTimeWeight

theorem continuous_fixed_family_of_pair_contraction
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    (T : P → X → X) (z : P → X)
    (hT : ∀ x, Continuous (fun p => T p x))
    (hz : ∀ p, T p (z p) = z p)
    (hpair : ∀ p q, dist (T p (z p)) (T p (z q)) ≤ (1 / 2 : ℝ) * dist (z p) (z q)) :
    Continuous z := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ q in 𝓝 p, dist (T q (z p)) (T p (z p)) < ε / 2 :=
    (hT (z p)).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [he] with q hq
  have ht := dist_triangle (T q (z q)) (T q (z p)) (T p (z p))
  rw [hz q, hz p] at ht
  have hp := hpair q p
  rw [hz q] at hp
  rw [hz p] at hq
  linarith

theorem continuous_expandingMild_family
    {P : Type*} [TopologicalSpace P] (a b k T K : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (F : P → C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (hF : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => F z.1 z.2))
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀)
    (u : P → C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ p, u p = expandingPicard a b k (L p).1 T ha hk (L p).2 hT
      (F p) (u₀ p) (u p))
    (hlocal : ∀ p q t,
      ‖F p (t, u p t) - F p (t, u q t)‖ ≤ K * ‖u p t - u q t‖) :
    Continuous u := by
  let η := 2 * K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  let z : P → C(Icc (0 : ℝ) T, FourierL2) :=
    fun p => expandingTimeWeight T (-η) (u p)
  let A : P → C(Icc (0 : ℝ) T, FourierL2) → C(Icc (0 : ℝ) T, FourierL2) :=
    fun p => expandingBieleckiPicard a b k (L p).1 T η ha hk (L p).2 hT (F p) (u₀ p)
  have hA : ∀ x, Continuous (fun p => A p x) := by
    intro x
    dsimp only [A]
    exact (continuous_expandingBieleckiPicard_family a b k T η ha hk hT L hL F hF
      u₀ hu₀).comp (continuous_id.prodMk continuous_const)
  have hfix : ∀ p, A p (z p) = z p := by
    intro p
    dsimp only [A, z]
    rw [expandingBieleckiPicard]
    rw [expandingTimeWeight_cancel, ← hu p]
  have hpair : ∀ p q, dist (A p (z p)) (A p (z q)) ≤
      (1 / 2 : ℝ) * dist (z p) (z q) := by
    intro p q
    have hb := expandingBieleckiPicard_pair_dist_le a b k (L p).1 T η ha hk (L p).2
      hT hη (F p) (u₀ p) K hK (z p) (z q) (by
        intro t
        simpa only [z, expandingTimeWeight_cancel] using hlocal p q t)
    exact hb.trans (mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hη).mpr (by dsimp [η]; linarith)) dist_nonneg)
  have hz : Continuous z := continuous_fixed_family_of_pair_contraction A z hA hfix hpair
  have hc := (continuous_expandingTimeWeight T η).comp hz
  simpa only [Function.comp_def, z, expandingTimeWeight_cancel] using hc

theorem continuous_expandingMild_bounded_family
    {P : Type*} [TopologicalSpace P] (a b k T R K : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (F : P → C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (hF : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => F z.1 z.2))
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀)
    (u : P → C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ p, u p = expandingPicard a b k (L p).1 T ha hk (L p).2 hT
      (F p) (u₀ p) (u p))
    (hub : ∀ p t, ‖u p t‖ ≤ R)
    (hlocal : ∀ p t x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖F p (t, x) - F p (t, y)‖ ≤ K * ‖x - y‖) :
    Continuous u :=
  continuous_expandingMild_family a b k T K ha hk hT hK L hL F hF u₀ hu₀ u hu
    (fun p q t => hlocal p t (u p t) (u q t) (hub p t) (hub q t))

end DefocusingNLS

end OAI
