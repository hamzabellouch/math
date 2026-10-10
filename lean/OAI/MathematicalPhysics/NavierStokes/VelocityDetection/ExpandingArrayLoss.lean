import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffRetention
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayTrajectories
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffCutoffZeroOnUpper

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses MovingCutoff SmoothProfiles SpatialCalculus
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))

def loss : ℝ := ν * 3000 * ((initialRadius ν (K₀ N b m) (D b))⁻¹ ^ 2 +
  ∑' n : ℕ, duration ν (K₀ N b m) (D b) n / radius ν (K₀ N b m) (D b) n ^ 2)

include hb in

theorem loss_lt (hν : 0 < ν) : loss (N := N) (b := b) ν m < (1 / 24 : ℝ) :=
  total_loss_lt hν (K₀_nonneg N b m) (D_ge_one hb)

include hb in

theorem loading_loss_le_loss (hν : 0 < ν) :
    ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2 ≤ loss (N := N) (b := b) ν m := by
  have heq : ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2 =
      ν * 3000 * (initialRadius ν (K₀ N b m) (D b))⁻¹ ^ 2 := by
    simp only [radius, pow_zero, mul_one, inv_pow, div_eq_mul_inv]
  rw [heq, loss, mul_add]
  have hs : 0 ≤ ∑' n : ℕ, duration ν (K₀ N b m) (D b) n /
      radius ν (K₀ N b m) (D b) n ^ 2 :=
    tsum_nonneg (fun n => (loss_term_bound hν (K₀_nonneg N b m) (D_ge_one hb) n).1)
  have : 0 ≤ ν * 3000 * (∑' n : ℕ, duration ν (K₀ N b m) (D b) n /
      radius ν (K₀ N b m) (D b) n ^ 2) := by positivity
  linarith

theorem field_slice_component (hν : 0 < ν) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun X => field hb table terminal ν m t X i) :=
  ((contDiff_apply ℝ ℝ i).comp
    (SpatialCalculus.contDiff_slice (contDiff_field hb table terminal ν m hν) t)).of_le (by simp)

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses MovingCutoff SmoothProfiles SpatialCalculus
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))
variable (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) ρ t X =
        ν * laplacian ρ t X + impulse (point hb table terminal ν m c₀ 0) t X)
    (hρinit : ∀ X, ρ 0 X = 0)
    (hρint : ∀ t, 0 ≤ t → Integrable (ρ t))
    (hρnonneg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t)

include hν hρ heq hρinit hρint hρnonneg hmass

theorem retained_loading {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ X, ρ t X) - capture (radius ν (K₀ N b m) (D b) 0)
        (fun _ => point hb table terminal ν m c₀ 0) ρ t ≤
      ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2 := by
  have hR : 0 < radius ν (K₀ N b m) (D b) 0 :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) 0)
  have hu (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) : 0 ≤ s := hs.1.le
  have h := retention_on_interval (ν := ν)
    (R := radius ν (K₀ N b m) (D b) 0)
    (a := field hb table terminal ν m) (g := impulse (point hb table terminal ν m c₀ 0))
    (c := fun _ => point hb table terminal ν m c₀ 0) (M := step)
    hR hν.le ht.1 hρ contDiff_const Real.smoothTransition.continuous.continuousOn
    (fun s _ => by rw [integral_impulse]; exact (differentiable_step s).hasDerivAt)
    (fun s _ => field_slice_component hb table terminal ν m hν s)
    (fun s _ => (contDiff_impulse (point hb table terminal ν m c₀ 0)).continuous.comp
      (continuous_const.prodMk continuous_id))
    (fun s _ X => divergence_field hb table terminal ν m hν s X)
    (fun s hs X => heq s (hu s hs) X)
    (fun s hs X _ => by
      rw [field_at_rest hb table terminal ν m hν (hs.2.le.trans ht.2) X]
      symm
      exact deriv_const s _)
    (fun s hs => hρint s (hu s hs)) (fun s hs => hρnonneg s (hu s hs))
    (fun s hs => by rw [hmass s (hu s hs)]; exact Real.smoothTransition.le_one s)
    (fun s _ X hX i => by
      have hsupport := (impulse_support_bound (point hb table terminal ν m c₀ 0) X s hX).2.2 i
      have hlarge := radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) 0
      linarith)
  have hz : capture (radius ν (K₀ N b m) (D b) 0)
      (fun _ => point hb table terminal ν m c₀ 0) ρ 0 = 0 := by
    simp only [capture, hρinit, mul_zero, integral_zero]
  rw [hz, show step 0 = 0 from Real.smoothTransition.zero_of_nonpos le_rfl, zero_sub,
    sub_zero, ← hmass t ht.1] at h
  have hm := mul_le_mul_of_nonneg_left ht.2 (by positivity :
    0 ≤ ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2)
  exact h.trans (by simpa using hm)

theorem retained_at_loading_end :
    step (startTime ν (K₀ N b m) (D b) 0) -
      capture (radius ν (K₀ N b m) (D b) 0) (runPath hb table terminal ν m c₀ 0) ρ
        (startTime ν (K₀ N b m) (D b) 0) ≤
      ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2 := by
  have hc : capture (radius ν (K₀ N b m) (D b) 0)
      (runPath hb table terminal ν m c₀ 0) ρ (startTime ν (K₀ N b m) (D b) 0) =
      capture (radius ν (K₀ N b m) (D b) 0)
      (fun _ => point hb table terminal ν m c₀ 0) ρ 1 := by
    unfold capture
    rw [runPath_start]
    rfl
  rw [hc]
  change step 1 - _ ≤ _
  rw [← hmass 1 (by norm_num)]
  exact retained_loading hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass ⟨by norm_num, le_rfl⟩

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses MovingCutoff SmoothProfiles SpatialCalculus
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))
variable (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) ρ t X =
        ν * laplacian ρ t X + impulse (point hb table terminal ν m c₀ 0) t X)
    (hρinit : ∀ X, ρ 0 X = 0)
    (hρint : ∀ t, 0 ≤ t → Integrable (ρ t))
    (hρnonneg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t)

include hν hρ heq hρinit hρint hρnonneg hmass
variable (hm : 1 ≤ m)
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (hterm : NoOutgoing table terminal)

include hm hc₀ hdir hin hterm

theorem retained_stages {n : ℕ}
    (hactive : ∀ k ≤ n, (lookup hb table (orbit hb table c₀ k)).isSome)
    {t : ℝ} (ht : t ∈ Icc (startTime ν (K₀ N b m) (D b) n)
      (startTime ν (K₀ N b m) (D b) (n + 1))) :
    (∫ X, ρ t X) - capture (radius ν (K₀ N b m) (D b) n)
      (runPath hb table terminal ν m c₀ n) ρ t ≤ loss (N := N) (b := b) ν m := by
  have hR (k : ℕ) : 0 < radius ν (K₀ N b m) (D b) k :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) k)
  have hτ (k : ℕ) : startTime ν (K₀ N b m) (D b) k ≤ startTime ν (K₀ N b m) (D b) (k + 1) :=
    (startTime_strictMono hν (K₀_nonneg N b m) (D_ge_one hb)).monotone (Nat.le_succ k)
  have hu (k : ℕ) (s : ℝ) (hs : s ∈ Icc (startTime ν (K₀ N b m) (D b) k)
      (startTime ν (K₀ N b m) (D b) (k + 1))) : 1 ≤ s := by
    linarith [startTime_ge hν (K₀_nonneg N b m) (D_ge_one hb) k,
      Nat.cast_nonneg (α := ℝ) k, hs.1]
  have loss_eq (k : ℕ) :
      (ν * 3000 / radius ν (K₀ N b m) (D b) k ^ 2) *
        (startTime ν (K₀ N b m) (D b) (k + 1) - startTime ν (K₀ N b m) (D b) k) =
      ν * 3000 * (duration ν (K₀ N b m) (D b) k / radius ν (K₀ N b m) (D b) k ^ 2) := by
    rw [startTime, add_sub_cancel_left]
    ring
  have hsummable : Summable (fun k => (ν * 3000 / radius ν (K₀ N b m) (D b) k ^ 2) *
      (startTime ν (K₀ N b m) (D b) (k + 1) - startTime ν (K₀ N b m) (D b) k)) := by
    simp_rw [loss_eq]
    exact (summable_loss hν (K₀_nonneg N b m) (D_ge_one hb)).mul_left _
  have h := retention_le_series (ν := ν)
    (R := radius ν (K₀ N b m) (D b)) (τ := startTime ν (K₀ N b m) (D b))
    (a := field hb table terminal ν m) (g := impulse (point hb table terminal ν m c₀ 0))
    (c := runPath hb table terminal ν m c₀) (M := step)
    hν.le hR hτ (radius_next_ge hν (K₀_nonneg N b m) (D_ge_one hb)) hρ
    (fun k => (contDiff_runPath hb table terminal ν m c₀ k).of_le (by simp))
    (runPath_joins hb table terminal ν m c₀ hν)
    (fun _ => Real.smoothTransition.continuous.continuousOn)
    (fun _ s _ => by rw [integral_impulse]; exact (differentiable_step s).hasDerivAt)
    (fun _ s _ => field_slice_component hb table terminal ν m hν s)
    (fun _ s _ => (contDiff_impulse (point hb table terminal ν m c₀ 0)).continuous.comp
      (continuous_const.prodMk continuous_id))
    (fun _ s _ X => divergence_field hb table terminal ν m hν s X)
    (fun k s hs X => heq s (by linarith [hu k s ⟨hs.1.le, hs.2.le⟩]) X)
    (fun k hk s hs X hX => runPath_plateau hb table terminal ν m c₀ hm hc₀ hν hdir hin hterm
      k (hactive k hk) ⟨hs.1.le, hs.2.le⟩ X hX)
    (fun k s hs => hρint s (by linarith [hu k s hs]))
    (fun k s hs => hρnonneg s (by linarith [hu k s hs]))
    (fun k s hs => by
      rw [hmass s (by linarith [hu k s ⟨hs.1.le, hs.2.le⟩])]
      exact Real.smoothTransition.le_one s)
    (fun k s hs X hX _ => by
      have hz := impulse_zero_of_time_one_le (point hb table terminal ν m c₀ 0)
        (hu k s ⟨hs.1.le, hs.2.le⟩)
      exact False.elim (hX (congrFun hz X))) hsummable ht
  have hload := retained_at_loading_end hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
  rw [← hmass t (by linarith [hu n t ht])] at h
  simp_rw [loss_eq] at h
  rw [tsum_mul_left] at h
  have hbudget : loss (N := N) (b := b) ν m = ν * 3000 / radius ν (K₀ N b m) (D b) 0 ^ 2 +
      ν * 3000 * (∑' k : ℕ, duration ν (K₀ N b m) (D b) k / radius ν (K₀ N b m) (D b) k ^ 2) := by
    simp only [loss, mul_add, radius, pow_zero, mul_one, inv_pow, div_eq_mul_inv]
  rw [hbudget]
  linarith

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses MovingCutoff SmoothProfiles SpatialCalculus
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))
variable (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) ρ t X =
        ν * laplacian ρ t X + impulse (point hb table terminal ν m c₀ 0) t X)
    (hρinit : ∀ X, ρ 0 X = 0)
    (hρint : ∀ t, 0 ≤ t → Integrable (ρ t))
    (hρnonneg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t)

include hν hρ heq hρinit hρint hρnonneg hmass
variable (hm : 1 ≤ m)
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (hterm : NoOutgoing table terminal)

include hm hc₀ hdir hin hterm
variable (hcont : Continues hb table terminal c₀)

include hcont

theorem nonterminal_mass_small (hnever : ¬ Reaches hb table terminal c₀)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ X in Observation.upperHalfPlane, ρ t X) < (1 / 4 : ℝ) := by
  have hn (k : ℕ) : (orbit hb table c₀ k).state ≠ terminal := by
    intro he
    exact hnever ⟨k, he⟩
  have hactive (k : ℕ) : (lookup hb table (orbit hb table c₀ k)).isSome := hcont k (hn k)
  have hR (k : ℕ) : 0 < radius ν (K₀ N b m) (D b) k :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) k)
  by_cases ht₁ : t ≤ 1
  · apply Cutoff.upper_mass_small (hR 0) (hρint t ht) (hρnonneg t ht)
      (c := point hb table terminal ν m c₀ 0)
      (δ := loss (N := N) (b := b) ν m)
    · have hc : point hb table terminal ν m c₀ 0 1 = -spacing ν (K₀ N b m) (D b) 0 := by
        simp only [point, sign, ite_eq_right (hn 0), neg_one_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hc, spacing]
      linarith [hR 0]
    · exact loss_lt hb ν m hν
    · exact (retained_loading hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
        ⟨ht, ht₁⟩).trans (loading_loss_le_loss hb ν m hν)
  · obtain ⟨n, hstage⟩ := time_in_stage hν (K₀_nonneg N b m) (D_ge_one hb) (le_of_not_ge ht₁)
    apply Cutoff.upper_mass_small (hR n) (hρint t ht) (hρnonneg t ht)
      (c := runPath hb table terminal ν m c₀ n t)
      (δ := loss (N := N) (b := b) ν m)
    · have hneg := runPath_negative hb table terminal ν m c₀ hm hc₀ hν hterm n
        (hactive n) (hn (n + 1)) t
      rw [spacing] at hneg
      linarith [hR n]
    · exact loss_lt hb ν m hν
    · exact retained_stages hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
        hm hc₀ hdir hin hterm (fun k _ => hactive k) hstage

theorem terminal_mass_large (hinit : c₀.state ≠ terminal)
    (hreach : Reaches hb table terminal c₀) :
    ∃ t : ℝ, 0 ≤ t ∧ (3 / 4 : ℝ) < ∫ X in Observation.upperHalfPlane, ρ t X := by
  let hex : ∃ n, (orbit hb table c₀ n).state = terminal := hreach
  have hzero : Nat.find hex ≠ 0 := by
    intro hz
    have h := Nat.find_spec hex
    rw [hz, orbit_zero] at h
    exact hinit h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hfirst : (orbit hb table c₀ (n + 1)).state = terminal := by
    simpa only [hn] using Nat.find_spec hex
  have hactive (k : ℕ) (hk : k ≤ n) : (lookup hb table (orbit hb table c₀ k)).isSome :=
    hcont k (Nat.find_min hex (by omega))
  let t := startTime ν (K₀ N b m) (D b) (n + 1)
  have ht₁ : 1 ≤ t := by
    have h := startTime_ge hν (K₀_nonneg N b m) (D_ge_one hb) (n + 1)
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
  have ht : 0 ≤ t := by linarith
  have hR : 0 < radius ν (K₀ N b m) (D b) n :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n)
  refine ⟨t, ht, ?_⟩
  apply Cutoff.upper_mass_large hR (hρint t ht) (hρnonneg t ht)
      (c := runPath hb table terminal ν m c₀ n t)
      (δ := loss (N := N) (b := b) ν m)
  · dsimp [t]
    rw [runPath_end hb table terminal ν m c₀ hν]
    have hc : point hb table terminal ν m c₀ (n + 1) 1 =
        spacing ν (K₀ N b m) (D b) (n + 1) := by
      simp only [point, sign, hfirst, ite_true, one_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hc, spacing]
    linarith [radius_next_ge hν (K₀_nonneg N b m) (D_ge_one hb) n]
  · exact loss_lt hb ν m hν
  · rw [hmass t ht]
    exact Real.smoothTransition.one_of_one_le ht₁
  · apply retained_stages hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
      hm hc₀ hdir hin hterm hactive
    exact ⟨(startTime_strictMono hν (K₀_nonneg N b m) (D_ge_one hb)).monotone (Nat.le_succ n), le_rfl⟩

theorem scalar_detection (hinit : c₀.state ≠ terminal) :
    Observation.planeEvent (liftVelocity (field hb table terminal ν m) ρ) ↔
      Reaches hb table terminal c₀ := by
  rw [Observation.planeEvent_lift]
  constructor
  · rintro ⟨t, ht, hmarg⟩
    by_contra hnever
    have h := nonterminal_mass_small hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
      hm hc₀ hdir hin hterm hcont hnever ht
    linarith
  · intro hreach
    obtain ⟨t, ht, hmarg⟩ := terminal_mass_large hb table terminal ν m c₀ hν hρ heq hρinit hρint hρnonneg hmass
      hm hc₀ hdir hin hterm hcont hinit hreach
    exact ⟨t, ht, lt_trans (by norm_num) hmarg⟩

end VelocityDetection.ExpandingArray
end

end OAI
