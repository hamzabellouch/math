import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffRetention
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayTrajectories
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffCutoffZeroOnUpper
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingSupport
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HistoryRouting

namespace OAI

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding MovingCutoff SmoothProfiles SpatialCalculus

structure Trace (A : RoutingData) where
  address : ℕ → ℕ
  stopped : ℕ → Bool
  instruction : ∀ n, stopped n = false → A.Instruction n
  source_eq : ∀ n h, A.source n (instruction n h) = address n
  target_eq : ∀ n h, A.target n (instruction n h) = address (n + 1)
  sign_eq : ∀ n h, A.sign n (instruction n h) = if stopped (n + 1) then 1 else -1

end VelocityDetection.RoutingArray
end

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding MovingCutoff SmoothProfiles SpatialCalculus
variable (A : RoutingData) (ν : ℝ) (tr : Trace A)

def Trace.sign {A : RoutingData} (tr : Trace A) (n : ℕ) : ℝ := if tr.stopped n then 1 else -1

def Trace.Stops {A : RoutingData} (tr : Trace A) : Prop := ∃ n, tr.stopped n = true

def point (n : ℕ) : Coord 2 :=
  ![spacing ν A.K A.D n * tr.address n, tr.sign n * spacing ν A.K A.D n]

def runPath (n : ℕ) : ℝ → Coord 2 :=
  CenterPaths.signedCenter (startTime ν A.K A.D n) (duration ν A.K A.D n)
    (spacing ν A.K A.D n) (spacing ν A.K A.D (n + 1))
    (tr.sign n) (tr.sign (n + 1)) (tr.address n) (tr.address (n + 1))

@[fun_prop] theorem contDiff_runPath (n : ℕ) : ContDiff ℝ ∞ (runPath A ν tr n) :=
  CenterPaths.contDiff_signedCenter _ _ _ _ _ _ _ _

theorem runPath_start (n : ℕ) :
    runPath A ν tr n (startTime ν A.K A.D n) = point A ν tr n :=
  CenterPaths.signed_start _ _ _ _ _ _ _ _

theorem runPath_end (hν : 0 < ν) (n : ℕ) :
    runPath A ν tr n (startTime ν A.K A.D (n + 1)) = point A ν tr (n + 1) :=
  CenterPaths.signed_end
    (lt_of_lt_of_le zero_lt_one (duration_ge_one hν A.K_nonneg A.D_ge_one n)) _ _ _ _ _ _ _

theorem runPath_joins (hν : 0 < ν) (n : ℕ) :
    runPath A ν tr n (startTime ν A.K A.D (n + 1)) =
      runPath A ν tr (n + 1) (startTime ν A.K A.D (n + 1)) := by
  rw [runPath_end A ν tr hν, runPath_start]

theorem runPath_eq_installed (n : ℕ) (h : tr.stopped n = false) :
    runPath A ν tr n = path A ν n (tr.instruction n h) := by
  unfold runPath
  have hs : tr.sign n = -1 := by simp [Trace.sign, h]
  rw [hs, CenterPaths.signed_source_negative]
  simp only [path, tr.source_eq n h, tr.target_eq n h, tr.sign_eq n h, Trace.sign]

theorem runPath_plateau (hν : 0 < ν) (n : ℕ) (h : tr.stopped n = false) {t : ℝ}
    (ht : t ∈ Icc (startTime ν A.K A.D n) (startTime ν A.K A.D (n + 1)))
    (X : Coord 2) (hX : ∀ i, |X i - runPath A ν tr n t i| ≤ radius ν A.K A.D n) :
    field A ν t X = deriv (runPath A ν tr n) t := by
  rw [runPath_eq_installed A ν tr n h] at hX ⊢
  exact field_plateau A ν hν n (tr.instruction n h) ht X hX

theorem runPath_negative (hν : 0 < ν) (n : ℕ) (h : tr.stopped n = false)
    (hn : tr.stopped (n + 1) = false) (t : ℝ) :
    runPath A ν tr n t 1 ≤ -spacing ν A.K A.D n := by
  rw [runPath_eq_installed A ν tr n h]
  apply path_negative A ν hν
  simp only [tr.sign_eq n h, hn, Bool.false_eq_true, ↓reduceIte]

def loss : ℝ := ν * 3000 * ((initialRadius ν A.K A.D)⁻¹ ^ 2 +
  ∑' n : ℕ, duration ν A.K A.D n / radius ν A.K A.D n ^ 2)

theorem loss_lt (hν : 0 < ν) : loss A ν < (1 / 24 : ℝ) :=
  total_loss_lt hν A.K_nonneg A.D_ge_one

theorem loading_loss_le_loss (hν : 0 < ν) :
    ν * 3000 / radius ν A.K A.D 0 ^ 2 ≤ loss A ν := by
  have heq : ν * 3000 / radius ν A.K A.D 0 ^ 2 =
      ν * 3000 * (initialRadius ν A.K A.D)⁻¹ ^ 2 := by
    simp only [radius, pow_zero, mul_one, inv_pow, div_eq_mul_inv]
  rw [heq, loss, mul_add]
  have hs : 0 ≤ ∑' n : ℕ, duration ν A.K A.D n /
      radius ν A.K A.D n ^ 2 :=
    tsum_nonneg (fun n => (loss_term_bound hν A.K_nonneg A.D_ge_one n).1)
  have : 0 ≤ ν * 3000 * (∑' n : ℕ, duration ν A.K A.D n /
      radius ν A.K A.D n ^ 2) := by positivity
  linarith

end VelocityDetection.RoutingArray
end

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding MovingCutoff SmoothProfiles SpatialCalculus
variable (A : RoutingData) (ν : ℝ) (tr : Trace A)
variable (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field A ν) ρ t X =
        ν * laplacian ρ t X + impulse (point A ν tr 0) t X)
    (hρinit : ∀ X, ρ 0 X = 0)
    (hρint : ∀ t, 0 ≤ t → Integrable (ρ t))
    (hρnonneg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t)

include hν hρ heq hρinit hρint hρnonneg hmass

theorem retained_loading {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ X, ρ t X) - capture (radius ν A.K A.D 0)
        (fun _ => point A ν tr 0) ρ t ≤
      ν * 3000 / radius ν A.K A.D 0 ^ 2 := by
  have hR : 0 < radius ν A.K A.D 0 :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one 0)
  have hu (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) : 0 ≤ s := hs.1.le
  have h := retention_on_interval (ν := ν)
    (R := radius ν A.K A.D 0)
    (a := field A ν) (g := impulse (point A ν tr 0))
    (c := fun _ => point A ν tr 0) (M := step)
    hR hν.le ht.1 hρ contDiff_const Real.smoothTransition.continuous.continuousOn
    (fun s _ => by rw [integral_impulse]; exact (differentiable_step s).hasDerivAt)
    (fun s _ => field_slice_component A ν hν s)
    (fun s _ => (contDiff_impulse (point A ν tr 0)).continuous.comp
      (continuous_const.prodMk continuous_id))
    (fun s _ X => divergence_field A ν hν s X)
    (fun s hs X => heq s (hu s hs) X)
    (fun s hs X _ => by
      rw [field_at_rest A ν hν (hs.2.le.trans ht.2) X]
      symm
      exact deriv_const s _)
    (fun s hs => hρint s (hu s hs)) (fun s hs => hρnonneg s (hu s hs))
    (fun s hs => by rw [hmass s (hu s hs)]; exact Real.smoothTransition.le_one s)
    (fun s _ X hX i => by
      have hsupport := (impulse_support_bound (point A ν tr 0) X s hX).2.2 i
      have hlarge := radius_ge_one hν A.K_nonneg A.D_ge_one 0
      linarith)
  have hz : capture (radius ν A.K A.D 0)
      (fun _ => point A ν tr 0) ρ 0 = 0 := by
    simp only [capture, hρinit, mul_zero, integral_zero]
  rw [hz, show step 0 = 0 from Real.smoothTransition.zero_of_nonpos le_rfl, zero_sub,
    sub_zero, ← hmass t ht.1] at h
  have hm := mul_le_mul_of_nonneg_left ht.2 (by positivity :
    0 ≤ ν * 3000 / radius ν A.K A.D 0 ^ 2)
  exact h.trans (by simpa using hm)

theorem retained_at_loading_end :
    step (startTime ν A.K A.D 0) -
      capture (radius ν A.K A.D 0) (runPath A ν tr 0) ρ
        (startTime ν A.K A.D 0) ≤
      ν * 3000 / radius ν A.K A.D 0 ^ 2 := by
  have hc : capture (radius ν A.K A.D 0)
      (runPath A ν tr 0) ρ (startTime ν A.K A.D 0) =
      capture (radius ν A.K A.D 0)
      (fun _ => point A ν tr 0) ρ 1 := by
    unfold capture
    rw [runPath_start]
    rfl
  rw [hc]
  change step 1 - _ ≤ _
  rw [← hmass 1 (by norm_num)]
  exact retained_loading A ν tr hν hρ heq hρinit hρint hρnonneg hmass ⟨by norm_num, le_rfl⟩

theorem retained_stages {n : ℕ}
    (hactive : ∀ k ≤ n, tr.stopped k = false)
    {t : ℝ} (ht : t ∈ Icc (startTime ν A.K A.D n)
      (startTime ν A.K A.D (n + 1))) :
    (∫ X, ρ t X) - capture (radius ν A.K A.D n)
      (runPath A ν tr n) ρ t ≤ loss A ν := by
  have hR (k : ℕ) : 0 < radius ν A.K A.D k :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one k)
  have hτ (k : ℕ) : startTime ν A.K A.D k ≤ startTime ν A.K A.D (k + 1) :=
    (startTime_strictMono hν A.K_nonneg A.D_ge_one).monotone (Nat.le_succ k)
  have hu (k : ℕ) (s : ℝ) (hs : s ∈ Icc (startTime ν A.K A.D k)
      (startTime ν A.K A.D (k + 1))) : 1 ≤ s := by
    linarith [startTime_ge hν A.K_nonneg A.D_ge_one k,
      Nat.cast_nonneg (α := ℝ) k, hs.1]
  have loss_eq (k : ℕ) :
      (ν * 3000 / radius ν A.K A.D k ^ 2) *
        (startTime ν A.K A.D (k + 1) - startTime ν A.K A.D k) =
      ν * 3000 * (duration ν A.K A.D k / radius ν A.K A.D k ^ 2) := by
    rw [startTime, add_sub_cancel_left]
    ring
  have hsummable : Summable (fun k => (ν * 3000 / radius ν A.K A.D k ^ 2) *
      (startTime ν A.K A.D (k + 1) - startTime ν A.K A.D k)) := by
    simp_rw [loss_eq]
    exact (summable_loss hν A.K_nonneg A.D_ge_one).mul_left _
  have h := retention_le_series (ν := ν)
    (R := radius ν A.K A.D) (τ := startTime ν A.K A.D)
    (a := field A ν) (g := impulse (point A ν tr 0))
    (c := runPath A ν tr) (M := step)
    hν.le hR hτ (radius_next_ge hν A.K_nonneg A.D_ge_one) hρ
    (fun k => (contDiff_runPath A ν tr k).of_le (by simp))
    (runPath_joins A ν tr hν)
    (fun _ => Real.smoothTransition.continuous.continuousOn)
    (fun _ s _ => by rw [integral_impulse]; exact (differentiable_step s).hasDerivAt)
    (fun _ s _ => field_slice_component A ν hν s)
    (fun _ s _ => (contDiff_impulse (point A ν tr 0)).continuous.comp
      (continuous_const.prodMk continuous_id))
    (fun _ s _ X => divergence_field A ν hν s X)
    (fun k s hs X => heq s (by linarith [hu k s ⟨hs.1.le, hs.2.le⟩]) X)
    (fun k hk s hs X hX => runPath_plateau A ν tr hν
      k (hactive k hk) ⟨hs.1.le, hs.2.le⟩ X hX)
    (fun k s hs => hρint s (by linarith [hu k s hs]))
    (fun k s hs => hρnonneg s (by linarith [hu k s hs]))
    (fun k s hs => by
      rw [hmass s (by linarith [hu k s ⟨hs.1.le, hs.2.le⟩])]
      exact Real.smoothTransition.le_one s)
    (fun k s hs X hX _ => by
      have hz := impulse_zero_of_time_one_le (point A ν tr 0)
        (hu k s ⟨hs.1.le, hs.2.le⟩)
      exact False.elim (hX (congrFun hz X))) hsummable ht
  have hload := retained_at_loading_end A ν tr hν hρ heq hρinit hρint hρnonneg hmass
  rw [← hmass t (by linarith [hu n t ht])] at h
  simp_rw [loss_eq] at h
  rw [tsum_mul_left] at h
  have hbudget : loss A ν = ν * 3000 / radius ν A.K A.D 0 ^ 2 +
      ν * 3000 * (∑' k : ℕ, duration ν A.K A.D k / radius ν A.K A.D k ^ 2) := by
    simp only [loss, mul_add, radius, pow_zero, mul_one, inv_pow, div_eq_mul_inv]
  rw [hbudget]
  linarith

theorem nonterminal_mass_small (hnever : ¬ tr.Stops)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ X in Observation.upperHalfPlane, ρ t X) < (1 / 4 : ℝ) := by
  have hn (k : ℕ) : tr.stopped k = false := by
    cases h : tr.stopped k
    · rfl
    · exact False.elim (hnever ⟨k, h⟩)
  have hactive (k : ℕ) : tr.stopped k = false := hn k
  have hR (k : ℕ) : 0 < radius ν A.K A.D k :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one k)
  by_cases ht₁ : t ≤ 1
  · apply Cutoff.upper_mass_small (hR 0) (hρint t ht) (hρnonneg t ht)
      (c := point A ν tr 0)
      (δ := loss A ν)
    · have hc : point A ν tr 0 1 = -spacing ν A.K A.D 0 := by
        simp only [point, Trace.sign, hn 0, Bool.false_eq_true, ↓reduceIte, neg_one_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hc, spacing]
      linarith [hR 0]
    · exact loss_lt A ν hν
    · exact (retained_loading A ν tr hν hρ heq hρinit hρint hρnonneg hmass
        ⟨ht, ht₁⟩).trans (loading_loss_le_loss A ν hν)
  · obtain ⟨n, hstage⟩ := ExpandingArray.time_in_stage hν A.K_nonneg A.D_ge_one (le_of_not_ge ht₁)
    apply Cutoff.upper_mass_small (hR n) (hρint t ht) (hρnonneg t ht)
      (c := runPath A ν tr n t)
      (δ := loss A ν)
    · have hneg := runPath_negative A ν tr hν n
        (hactive n) (hn (n + 1)) t
      rw [spacing] at hneg
      linarith [hR n]
    · exact loss_lt A ν hν
    · exact retained_stages A ν tr hν hρ heq hρinit hρint hρnonneg hmass
        (fun k _ => hactive k) hstage

theorem terminal_mass_large (hinit : tr.stopped 0 = false)
    (hreach : tr.Stops) :
    ∃ t : ℝ, 0 ≤ t ∧ (3 / 4 : ℝ) < ∫ X in Observation.upperHalfPlane, ρ t X := by
  let hex : ∃ n, tr.stopped n = true := hreach
  have hzero : Nat.find hex ≠ 0 := by
    intro hz
    have h := Nat.find_spec hex
    rw [hz, hinit] at h
    cases h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hfirst : tr.stopped (n + 1) = true := by
    simpa only [hn] using Nat.find_spec hex
  have hactive (k : ℕ) (hk : k ≤ n) : tr.stopped k = false :=
    Bool.eq_false_iff.mpr (Nat.find_min hex (by omega))
  let t := startTime ν A.K A.D (n + 1)
  have ht₁ : 1 ≤ t := by
    have h := startTime_ge hν A.K_nonneg A.D_ge_one (n + 1)
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
  have ht : 0 ≤ t := by linarith
  have hR : 0 < radius ν A.K A.D n :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one n)
  refine ⟨t, ht, ?_⟩
  apply Cutoff.upper_mass_large hR (hρint t ht) (hρnonneg t ht)
      (c := runPath A ν tr n t)
      (δ := loss A ν)
  · dsimp [t]
    rw [runPath_end A ν tr hν]
    have hc : point A ν tr (n + 1) 1 =
        spacing ν A.K A.D (n + 1) := by
      simp only [point, Trace.sign, hfirst, ↓reduceIte, one_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hc, spacing]
    linarith [radius_next_ge hν A.K_nonneg A.D_ge_one n]
  · exact loss_lt A ν hν
  · rw [hmass t ht]
    exact Real.smoothTransition.one_of_one_le ht₁
  · apply retained_stages A ν tr hν hρ heq hρinit hρint hρnonneg hmass
      hactive
    exact ⟨(startTime_strictMono hν A.K_nonneg A.D_ge_one).monotone (Nat.le_succ n), le_rfl⟩

theorem scalar_detection (hinit : tr.stopped 0 = false) :
    Observation.planeEvent (liftVelocity (field A ν) ρ) ↔
      tr.Stops := by
  rw [Observation.planeEvent_lift]
  constructor
  · rintro ⟨t, ht, hmarg⟩
    by_contra hnever
    have h := nonterminal_mass_small A ν tr hν hρ heq hρinit hρint hρnonneg hmass
      hnever ht
    linarith
  · intro hreach
    obtain ⟨t, ht, hmarg⟩ := terminal_mass_large A ν tr hν hρ heq hρinit hρint hρnonneg hmass
      hinit hreach
    exact ⟨t, ht, lt_trans (by norm_num) hmarg⟩

end VelocityDetection.RoutingArray
end

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding MovingCutoff SmoothProfiles SpatialCalculus
variable (A : RoutingData) (ν : ℝ) (tr : Trace A)

theorem velocity_detection (hν : 0 < ν) (hinit : tr.stopped 0 = false) :
    Observation.planeEvent (velocity A ν hν (point A ν tr 0)) ↔ tr.Stops := by
  let p := point A ν tr 0
  have hρ := contDiff_scalarSolution A ν hν p
  obtain ⟨hpos, hint, hmass⟩ := scalarSolution_properties A ν hν p
  exact scalar_detection A ν tr hν (hρ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (fun t ht X => by
      rw [← JointCalculus.timeD_eq_deriv ht X (hρ.differentiable (by simp) (t, X))]
      exact scalarSolution_equation A ν hν p ht X)
    (scalarSolution_zero A ν hν p) (fun t _ => hint t) hpos hmass hinit

end VelocityDetection.RoutingArray
end

end OAI
