import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicSpatialForce
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.StageFlow

namespace OAI

/-! The logarithmic slowdown is extended smoothly through all negative times.
The given zero collar removes the apparent singularity of the logarithm. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology NNReal
open ShearFlows

namespace ForcedComputation

def slowFromRest (V : Velocity) : Velocity := fun y =>
  if y.1 ≤ 0 then 0 else (1 + y.1)⁻¹ • V (Real.log (1 + y.1), y.2)

theorem slowFromRest_before (V : Velocity) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    slowFromRest V (t, x) = 0 := by simp only [slowFromRest, ht, ite_true]

theorem slowFromRest_eq {V : Velocity} (hzero : ∀ x, V (0, x) = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) : slowFromRest V (t, x) = slowVelocity V (t, x) := by
  by_cases hp : t ≤ 0
  · have he : t = 0 := le_antisymm hp ht
    subst t
    simp [slowFromRest, slowVelocity, reparametrizedVelocity, logClock, hzero]
  · simp only [slowFromRest, hp, ite_false, slowVelocity, reparametrizedVelocity, logClock]

theorem slowFromRest_zero_collar {V : Velocity}
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    {t : ℝ} (ht : t < (1 / 64 : ℝ)) (x : Space) : slowFromRest V (t, x) = 0 := by
  by_cases hn : t ≤ 0
  · exact slowFromRest_before V hn x
  · have hp : 0 < 1 + t := by linarith
    have hl : Real.log (1 + t) < (1 / 32 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hp
      linarith
    simp only [slowFromRest, hn, ite_false, hzero _ hl x, smul_zero]

theorem slowFromRest_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0) :
    ContDiff ℝ ∞ (slowFromRest V) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hn : y.1 < (1 / 64 : ℝ)
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : Space)) y).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto y).eventually (eventually_lt_nhds hn)] with z hz
    exact slowFromRest_zero_collar hzero hz z.2
  · have hp : 0 < y.1 := by linarith
    have harg : 1 + y.1 ≠ 0 := by linarith
    have ha : ContDiffAt ℝ ∞ (fun z : SpaceTime => (1 + z.1)⁻¹) y :=
      (contDiffAt_const.add contDiffAt_fst).inv harg
    have hc : ContDiffAt ℝ ∞ (fun z : SpaceTime => (Real.log (1 + z.1), z.2)) y :=
      ((Real.contDiffAt_log.mpr harg).comp y (contDiffAt_const.add contDiffAt_fst)).prodMk
        contDiffAt_snd
    apply (ha.smul (hV.contDiffAt.comp y hc)).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto y).eventually (eventually_gt_nhds hp)] with z hz
    exact ite_eq_right (not_le.mpr hz)

theorem slowFromRest_periodic {L : ℝ} {V : Velocity} (hV : SpatiallyPeriodic L V) :
    SpatiallyPeriodic L (slowFromRest V) := by
  intro t x n
  by_cases ht : t ≤ 0
  · simp only [slowFromRest, ht, ite_true]
  · simp only [slowFromRest, ht, ite_false]
    rw [hV]

theorem slowFromRest_solenoidal {V : Velocity} (hV : Solenoidal V) :
    Solenoidal (slowFromRest V) := by
  intro t x
  by_cases ht : t ≤ 0
  · simp only [slowFromRest, ht, ite_true]
    simp [divergence, derivative]
  · simp only [slowFromRest, ht, ite_false]
    rw [divergence_smul, hV, mul_zero]

theorem slowFromRest_zero_advection {V : Velocity} (hV : ZeroAdvection V) :
    ZeroAdvection (slowFromRest V) := by
  intro t x
  by_cases ht : t ≤ 0
  · simp only [slowFromRest, ht, ite_true]
    simp [advection]
  · simp only [slowFromRest, ht, ite_false]
    rw [advection_smul, hV, smul_zero]

theorem slowFromRest_mean_zero {L : ℝ} {V : Velocity} (hV : HasZeroMean L V) :
    HasZeroMean L (slowFromRest V) := by
  intro t
  by_cases ht : t ≤ 0
  · simp only [slowFromRest, ht, ite_true]
    simp
  · simp only [slowFromRest, ht, ite_false]
    rw [MeasureTheory.integral_smul, hV, smul_zero]

theorem slowFromRest_solution {V : Velocity} {L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hper : SpatiallyPeriodic L V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hdiv : Solenoidal V) (hadv : ZeroAdvection V) (ν : ℝ) :
    IsClassicalSolution L ν (force ν (slowFromRest V)) (slowFromRest V) (fun _ => 0) :=
  velocity_solves_forced_NS (slowFromRest_smooth hV hzero)
    (slowFromRest_periodic hper) (slowFromRest_solenoidal hdiv)
    (slowFromRest_zero_advection hadv) (slowFromRest_before V le_rfl) ν

theorem slowFromRest_uniform_bound {V : Velocity} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, ‖V y‖ ≤ B) (y : SpaceTime) : ‖slowFromRest V y‖ ≤ B := by
  by_cases ht : y.1 ≤ 0
  · simpa only [slowFromRest, ht, ite_true, norm_zero] using hB
  · have hp : 0 < 1 + y.1 := by linarith
    have hi : (1 + y.1)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
    simp only [slowFromRest, ht, ite_false, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact (mul_le_mul_of_nonneg_left (hb _) (inv_pos.mpr hp).le).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hi hB)

theorem slowFromRest_lipschitz {V : Velocity} {K : ℝ≥0}
    (hK : ∀ t, LipschitzWith K (fun x => V (t, x))) (t : ℝ) :
    LipschitzWith K (fun x => slowFromRest V (t, x)) := by
  by_cases ht : t ≤ 0
  · have he : (fun x => slowFromRest V (t, x)) = fun _ => 0 :=
      funext (slowFromRest_before V ht)
    rw [he]
    exact (LipschitzWith.const (0 : Space)).weaken (zero_le)
  · have hp : 0 < 1 + t := by linarith
    have hi : (1 + t)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [slowFromRest, ht, ite_false, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    calc
      _ ≤ 1 * ‖V (Real.log (1 + t), x) - V (Real.log (1 + t), y)‖ :=
        mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      _ ≤ (K : ℝ) * ‖x - y‖ := by
        simpa only [one_mul, dist_eq_norm] using (hK (Real.log (1 + t))).dist_le_mul x y

theorem slowFromRest_materialFlow {V : Velocity} {L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hper : SpatiallyPeriodic L V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (fun x => V (t, x)))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖V y‖ ≤ B) :
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow L (slowFromRest V) Φ := by
  exact exists_materialFlow_of_bounded_lipschitz (B := ⟨B, hB⟩)
    (slowFromRest_lipschitz hK)
    (fun x => (slowFromRest_smooth hV hzero).continuous.comp
      (continuous_id.prodMk continuous_const))
    (fun t x => slowFromRest_uniform_bound hB hb (t, x)) (slowFromRest_periodic hper)

theorem slowFromRest_trace {V : Velocity} {L : ℝ}
    (hzero : ∀ x, V (0, x) = 0)
    {Φ Ψ : ℝ → Space → Space} (hΦ : IsMaterialFlow L V Φ)
    (hΨ : IsMaterialFlow L (slowFromRest V) Ψ)
    {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (fun x => slowFromRest V (t, x)))
    (x : Space) {t : ℝ} (ht : 0 ≤ t) : Ψ t x = Φ (logClock t) x := by
  have hc : ContinuousOn (fun s => Φ (logClock s) x) (Icc 0 t) := by
    apply (continuous_iff_continuousAt.mpr (fun s => (hΦ.ode s x).continuousAt)).comp_continuousOn
    apply ContinuousOn.log
    · fun_prop
    · intro s hs
      linarith [hs.1]
  apply hΨ.eqOn_of_candidate hK x (fun s => Φ (logClock s) x) hc
    (by simp only [logClock, add_zero, Real.log_one, hΦ.initial, hΨ.initial]) ?_ ⟨ht, le_rfl⟩
  intro s hs
  rw [slowFromRest_eq hzero hs.1]
  have hd := (hΦ.ode (logClock s) x).scomp s (logClock_hasDerivAt hs.1)
  simpa only [Function.comp_def, one_div, slowVelocity, reparametrizedVelocity] using hd

theorem slowFromRest_reaches_iff {V : Velocity} {L : ℝ}
    (hzero : ∀ x, V (0, x) = 0)
    {Φ Ψ : ℝ → Space → Space} (hΦ : IsMaterialFlow L V Φ)
    (hΨ : IsMaterialFlow L (slowFromRest V) Ψ)
    {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (fun x => V (t, x)))
    (x : Space) (O : Set Space) :
    Reaches (fun t => Ψ t x) O ↔ Reaches (fun t => Φ t x) O := by
  have he : Reaches (fun t => Ψ t x) O ↔ Reaches ((fun t => Φ t x) ∘ logClock) O := by
    constructor <;> rintro ⟨t, ht, hx⟩ <;> refine ⟨t, ht, ?_⟩
    · change Ψ t x ∈ O at hx
      change Φ (logClock t) x ∈ O
      rwa [slowFromRest_trace hzero hΦ hΨ (slowFromRest_lipschitz hK) x ht] at hx
    · change Φ (logClock t) x ∈ O at hx
      change Ψ t x ∈ O
      rwa [slowFromRest_trace hzero hΦ hΨ (slowFromRest_lipschitz hK) x ht]
  exact he.trans (logClock_reaches_iff _ _)

end ForcedComputation

end

end OAI
