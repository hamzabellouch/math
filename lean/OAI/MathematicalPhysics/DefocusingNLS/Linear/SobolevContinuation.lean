import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevIntervalUniqueness

namespace OAI

/-! # Uniform local lifespans and continuation of Sobolev interaction solutions -/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- Every bounded set of initial data has one common positive local lifespan, at every time. -/
theorem exists_uniform_sobolevInteraction_time (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t₀ : ℝ) (f₀ : FourierL2), ‖f₀‖ ≤ R →
      ∃ v : ℝ → FourierL2, v t₀ = f₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t := by
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m (R + 1) (by linarith)
  let δ : ℝ := 1 / (A + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro t₀ f₀ hf₀
  let τ₀ : Icc (t₀ - δ) (t₀ + δ) := ⟨t₀, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (schrodingerInteractionField k hk m)
      τ₀ 0 ⟨R + 1, by linarith⟩ ⟨R, hR⟩ ⟨A, hA⟩ ⟨K, hK⟩ := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro f hf g hg
      rw [dist_eq_norm, dist_eq_norm]
      change ‖schrodingerInteractionField k hk m t f - schrodingerInteractionField k hk m t g‖ ≤
        K * ‖f - g‖
      have hfn : ‖f‖ ≤ R + 1 := by
        rw [mem_closedBall, dist_zero_right] at hf
        change ‖f‖ ≤ R + 1 at hf
        exact hf
      have hgn : ‖g‖ ≤ R + 1 := by
        rw [mem_closedBall, dist_zero_right] at hg
        change ‖g‖ ≤ R + 1 at hg
        exact hg
      exact hlip t f g hfn hgn
    · intro f hf
      exact ((continuous_schrodingerInteractionField k hk m).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht f hf
      apply hbound t f
      rw [mem_closedBall, dist_zero_right] at hf
      change ‖f‖ ≤ R + 1 at hf
      exact hf
    · change A * max ((t₀ + δ) - t₀) (t₀ - (t₀ - δ)) ≤ (R + 1) - R
      have hmax : max ((t₀ + δ) - t₀) (t₀ - (t₀ - δ)) = δ := by
        have h1 : (t₀ + δ) - t₀ = δ := by ring
        have h2 : t₀ - (t₀ - δ) = δ := by ring
        rw [h1, h2, max_self]
      rw [hmax]
      have hr : (R + 1) - R = 1 := by ring
      rw [hr]
      dsimp [δ]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < A + 1)).2
      linarith
  obtain ⟨v, hv₀, hv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (x := f₀) (by
      change dist f₀ 0 ≤ R
      simpa only [dist_zero_right] using hf₀)
  refine ⟨v, hv₀, ?_⟩
  intro t ht
  exact (hv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- A right continuation is a classical solution across the endpoint agreeing on a left neighborhood. -/
def HasSobolevInteractionContinuation (k : ℝ) (hk : 6 < k) (m : ℕ)
    (v : ℝ → FourierL2) (T : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ w : ℝ → FourierL2,
    (∀ t ∈ Ioo (T - ε) (T + ε),
      HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t) ∧
    EqOn w v (Ioo (T - ε) T)

/-- A local solution started before the endpoint and lasting beyond it continues the original one. -/
theorem sobolevInteraction_continuation_from_overlap
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v w : ℝ → FourierL2)
    (a T t₀ δ : ℝ) (ht₀ : t₀ ∈ Ioo a T) (hT : T < t₀ + δ)
    (hv : ∀ t ∈ Ioo a T, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hw : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t)
    (heq : v t₀ = w t₀) : HasSobolevInteractionContinuation k hk m v T := by
  have hδ : 0 < δ := by linarith [ht₀.2]
  let ε := min (T - t₀) (t₀ + δ - T) / 2
  have hε : 0 < ε := by
    exact div_pos (lt_min (sub_pos.mpr ht₀.2) (sub_pos.mpr hT)) (by norm_num)
  have hleft : t₀ < T - ε := by
    have h := min_le_left (T - t₀) (t₀ + δ - T)
    dsimp [ε]
    linarith [ht₀.2]
  have hright : T + ε < t₀ + δ := by
    have h := min_le_right (T - t₀) (t₀ + δ - T)
    dsimp [ε]
    linarith
  have htbase : t₀ ∈ Ioo (max a (t₀ - δ)) T :=
    ⟨max_lt ht₀.1 (by linarith), ht₀.2⟩
  have he := sobolevInteractionSolution_unique_on_interval k hk m v w
    (max a (t₀ - δ)) T t₀ htbase
    (fun t ht => hv t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2⟩)
    (fun t ht => hw t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, ht.2.trans hT⟩) heq
  refine ⟨ε, hε, w, ?_, ?_⟩
  · intro t ht
    exact hw t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    exact (he ⟨by
      apply max_lt
      · linarith [ht₀.1, ht.1]
      · linarith [ht.1]
      , ht.2⟩).symm

/-- A finite right endpoint with bounded Sobolev norm is extendible. -/
theorem sobolevInteraction_continuation_of_bounded
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v : ℝ → FourierL2)
    (a T R : ℝ) (haT : a < T) (hR : 0 ≤ R)
    (hv : ∀ t ∈ Ioo a T, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hb : ∀ t ∈ Ioo a T, ‖v t‖ ≤ R) : HasSobolevInteractionContinuation k hk m v T := by
  obtain ⟨δ, hδ, hex⟩ := exists_uniform_sobolevInteraction_time k hk m R hR
  let d := min δ (T - a) / 2
  let t₀ := T - d
  have hd : 0 < d := by dsimp [d]; positivity
  have hda : d < T - a := by
    have h := min_le_right δ (T - a)
    dsimp [d]
    linarith
  have hdd : d < δ := by
    have h := min_le_left δ (T - a)
    dsimp [d]
    linarith
  have ht₀ : t₀ ∈ Ioo a T := by dsimp [t₀]; constructor <;> linarith
  obtain ⟨w, hw₀, hw⟩ := hex t₀ (v t₀) (hb t₀ ht₀)
  exact sobolevInteraction_continuation_from_overlap k hk m v w a T t₀ δ ht₀
    (by dsimp [t₀]; linarith) hv hw hw₀.symm

/-- A nonextendible finite endpoint forces the Sobolev norm to diverge. -/
theorem sobolevInteraction_norm_tendsto_atTop
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v : ℝ → FourierL2)
    (a T : ℝ) (haT : a < T)
    (hv : ∀ t ∈ Ioo a T, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hmax : ¬ HasSobolevInteractionContinuation k hk m v T) :
    Tendsto (fun t => ‖v t‖) (𝓝[<] T) atTop := by
  rw [Filter.tendsto_atTop]
  intro R
  obtain ⟨δ, hδ, hex⟩ := exists_uniform_sobolevInteraction_time k hk m (max R 0)
    (le_max_right _ _)
  have hb : max a (T - δ / 2) < T := max_lt haT (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hb] with t ht
  by_contra hn
  have hnorm : ‖v t‖ ≤ max R 0 := (le_of_lt (lt_of_not_ge hn)).trans (le_max_left _ _)
  have ht' : t ∈ Ioo a T := ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2⟩
  obtain ⟨w, hw₀, hw⟩ := hex t (v t) hnorm
  apply hmax
  exact sobolevInteraction_continuation_from_overlap k hk m v w a T t δ ht'
    (by have h := lt_of_le_of_lt (le_max_right _ _) ht.1; linarith) hv hw hw₀.symm

end DefocusingNLS

end OAI
