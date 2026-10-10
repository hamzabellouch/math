import Mathlib
import OAI.MathematicalPhysics.SheetFlows.ScheduledForce

namespace OAI

/-! SheetFlows trajectories. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def stageField {m : ℕ} (v : Fin m → Space → Space) (n : ℕ) : Space → Space :=
  if h : n < m then v ⟨n, h⟩ else 0

def stageState {m : ℕ} (v : Fin m → Space → Space) (a : Space) : ℕ → Space
  | 0 => a
  | n + 1 => stageState v a n + stageField v n (stageState v a n)

def stageIncrement {m : ℕ} (v : Fin m → Space → Space) (a : Space) (i : Fin m) : Space :=
  v i (stageState v a i.val)

@[simp] theorem stageField_fin {m : ℕ} (v : Fin m → Space → Space) (i : Fin m) :
    stageField v i.val = v i := by simp [stageField, i.isLt]

theorem stageState_succ {m : ℕ} (v : Fin m → Space → Space) (a : Space) (i : Fin m) :
    stageState v a (i.val + 1) = stageState v a i.val + stageIncrement v a i := by
  rw [stageState, stageField_fin]
  rfl

theorem stageState_eq_sum {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {n : ℕ} (hn : n ≤ m) :
    stageState v a n = a + ∑ i : Fin m, if i.val < n then stageIncrement v a i else 0 := by
  induction n with
  | zero => simp [stageState]
  | succ n ih =>
    have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have he (i : Fin m) :
        (if i.val < n + 1 then stageIncrement v a i else 0) =
        (if i.val < n then stageIncrement v a i else 0) +
        (if i = ⟨n, hnm⟩ then stageIncrement v a i else 0) := by
      by_cases hi : i.val < n
      · have hne : i ≠ ⟨n, hnm⟩ := by intro h; simp [h] at hi
        simp [hi, Nat.lt_succ_of_lt hi, hne]
      · by_cases hie : i = ⟨n, hnm⟩
        · subst i
          simp
        · have hin : ¬i.val < n + 1 := by
            have hv : i.val ≠ n := by simpa [Fin.ext_iff] using hie
            omega
          simp [hi, hie, hin]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← add_assoc, ← ih (Nat.le_of_succ_le hn), ← stageState_succ v a ⟨n, hnm⟩]

theorem stageState_final {m : ℕ} (v : Fin m → Space → Space) (a : Space) :
    stageState v a m = a + ∑ i : Fin m, stageIncrement v a i := by
  simpa only [Fin.is_lt, ite_true] using stageState_eq_sum v a (le_refl m)

def launchPath {m : ℕ} (v : Fin m → Space → Space) (a : Space) (t : ℝ) : Space :=
  a + ∑ i : Fin m, pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i

theorem launchPath_start {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {t : ℝ} (ht : t ≤ 1/4) : launchPath v a t = a := by
  have he (i : Fin m) : pulseClock (slotLeft m i) (slotRight m i) t = 0 :=
    pulseClock_zero (slot_bounds i).2.1 (ht.trans (slot_bounds i).1)
  simp [launchPath, he]

theorem launchPath_finish {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {t : ℝ} (ht : 3/4 ≤ t) : launchPath v a t = stageState v a m := by
  have he (i : Fin m) : pulseClock (slotLeft m i) (slotRight m i) t = 1 :=
    pulseClock_one (slot_bounds i).2.1 ((slot_bounds i).2.2.trans ht)
  simp only [launchPath, he, one_smul, stageState_final]

theorem launchPath_contDiff {m : ℕ} (v : Fin m → Space → Space) (a : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (launchPath v a) := by
  exact contDiff_const.add (ContDiff.sum (fun i _ =>
    (pulseClock_contDiff _ _).smul contDiff_const))

theorem launchPath_active {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (i : Fin m) {t : ℝ} (ht : t ∈ Set.Icc (slotLeft m i) (slotRight m i)) :
    launchPath v a t = stageState v a i.val +
      pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i := by
  classical
  have he (j : Fin m) :
      pulseClock (slotLeft m j) (slotRight m j) t • stageIncrement v a j =
      (if j.val < i.val then stageIncrement v a j else 0) +
      (if j = i then
        pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i else 0) := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hjt := (slot_ordered hji).le.trans ht.1
      rw [pulseClock_one (slot_bounds j).2.1 hjt]
      simp [hji, hji.ne]
    · simp
    · have hjt := ht.2.trans (slot_ordered hij).le
      rw [pulseClock_zero (slot_bounds j).2.1 hjt]
      simp [not_lt_of_gt hij, hij.ne']
  unfold launchPath
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => he j)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← add_assoc, ← stageState_eq_sum v a i.isLt.le]

def StraightInvariant (v : Space → Space) : Prop :=
  ∀ (x : Space) (c : ℝ), v (x + c • v x) = v x

theorem axialField_straightInvariant (i : Fin 3) (g : Space → ℝ) :
    StraightInvariant (axialField i (fun _ => g) 0) := by
  intro x c
  simp only [axialField, map_add, map_smul, eraseAxis_basis, smul_zero, add_zero]

theorem launchPath_hasDerivAt {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) (t : ℝ) :
    HasDerivAt (launchPath v a)
      (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • v i (launchPath v a t)) t := by
  have h : HasDerivAt (launchPath v a)
      (∑ i, localPulse (slotLeft m i) (slotRight m i) t • stageIncrement v a i) t := by
    convert (hasDerivAt_const t a).fun_add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (((pulseClock_contDiff (slotLeft m i) (slotRight m i)).differentiable (by simp)
          t).hasDerivAt.smul_const (stageIncrement v a i)))) using 1 <;>
      first | rfl | simp only [zero_add, localPulse]
  suffices he : (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • v i (launchPath v a t)) =
      (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • stageIncrement v a i) by
    rw [he]
    exact h
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : localPulse (slotLeft m i) (slotRight m i) t = 0
  · rw [hi, zero_smul, zero_smul]
  · have hleft : slotLeft m i < t := by
      by_contra h
      exact hi (localPulse_zero_left (slot_bounds i).2.1 (le_of_not_gt h))
    have hright : t < slotRight m i := by
      by_contra h
      exact hi (localPulse_zero_right (slot_bounds i).2.1 (le_of_not_gt h))
    rw [launchPath_active v a i ⟨hleft.le, hright.le⟩]
    exact congrArg (localPulse (slotLeft m i) (slotRight m i) t • ·)
      (hv i (stageState v a i.val) _)

theorem launchPath_periodic_ode {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    HasDerivAt (launchPath v a) (scheduleVelocity v t (launchPath v a t)) t := by
  have he (i : Fin m) : scheduledPulse m i t = localPulse (slotLeft m i) (slotRight m i) t :=
    periodicPulse_on_chart (slot_bounds i).2.1 (by linarith [(slot_bounds i).1])
      (by linarith [(slot_bounds i).2.2]) ht
  simpa only [scheduleVelocity, he] using launchPath_hasDerivAt v hv a t

def periodState {m : ℕ} (v : Fin m → Space → Space) (a : Space) : ℕ → Space
  | 0 => a
  | n + 1 => stageState v (periodState v a n) m

def repeatedPath {m : ℕ} (v : Fin m → Space → Space) (a : Space) (t : ℝ) : Space :=
  launchPath v (periodState v a ⌊t⌋₊) (t - (⌊t⌋₊ : ℝ))

theorem repeatedPath_on_Ico {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    repeatedPath v a t = launchPath v (periodState v a n) (t - n) := by
  rw [repeatedPath, Nat.floor_eq_on_Ico n t ht]

theorem repeatedPath_on_collar {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    repeatedPath v a t = periodState v a n := by
  obtain ⟨hl, hr⟩ := abs_lt.mp ht
  cases n with
  | zero =>
    have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num at hr; linarith)
    simp only [repeatedPath, hf, Nat.cast_zero, sub_zero, periodState]
    exact launchPath_start v a (by norm_num at hr; linarith)
  | succ n =>
    by_cases hnt : ((n + 1 : ℕ) : ℝ) ≤ t
    · rw [repeatedPath_on_Ico v a (n+1) ⟨hnt, by linarith⟩]
      exact launchPath_start v _ hr.le
    · have htn : t < (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnt
      rw [repeatedPath_on_Ico v a n ⟨by push_cast at hl; linarith, htn⟩]
      change launchPath v (periodState v a n) (t - n) = stageState v (periodState v a n) m
      apply launchPath_finish
      push_cast at hl
      linarith

theorem repeatedPath_at_nat {m : ℕ} (v : Fin m → Space → Space) (a : Space) (n : ℕ) :
    repeatedPath v a (n : ℝ) = periodState v a n :=
  repeatedPath_on_collar v a n (by simp)

theorem repeatedPath_hasDerivAt_nat {m : ℕ} (v : Fin m → Space → Space) (a : Space) (n : ℕ) :
    HasDerivAt (repeatedPath v a) 0 (n : ℝ) := by
  apply (hasDerivAt_const (n : ℝ) (periodState v a n)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (n : ℝ) ∈ Set.Ioo ((n : ℝ) - 1/4) (n + 1/4) by
    constructor <;> linarith)] with t ht
  exact repeatedPath_on_collar v a n (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem scheduleVelocity_at_nat {m : ℕ} (v : Fin m → Space → Space) (n : ℕ) (x : Space) :
    scheduleVelocity v (n : ℝ) x = 0 := by
  obtain ⟨ε, hε, hz⟩ := scheduleVelocity_integerCollars v
  apply hz (n : ℤ)
  simpa using hε

theorem repeatedPath_hasDerivAt {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (repeatedPath v a) (scheduleVelocity v t (repeatedPath v a t)) t := by
  let n : ℕ := ⌊t⌋₊
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
  have htn : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  by_cases hnat : t = (n : ℝ)
  · rw [hnat, scheduleVelocity_at_nat]
    exact repeatedPath_hasDerivAt_nat v a n
  · have hnt' : (n : ℝ) < t := lt_of_le_of_ne hnt (Ne.symm hnat)
    have he : repeatedPath v a =ᶠ[𝓝 t]
        (fun s => launchPath v (periodState v a n) (s - n)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (n : ℝ) ((n : ℝ)+1) from
        ⟨hnt', htn⟩)] with s hs
      exact repeatedPath_on_Ico v a n ⟨hs.1.le, hs.2⟩
    have hp (x : Space) : scheduleVelocity v (t - n) x = scheduleVelocity v t x := by
      have hper : Function.Periodic (fun s => scheduleVelocity v s x) 1 :=
        fun s => scheduleVelocity_onePeriodic v s x
      simpa only [mul_one] using hper.sub_nat_mul_eq (x := t) n
    have hD := (launchPath_periodic_ode v hv (periodState v a n)
      (show t - (n : ℝ) ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr hnt, by linarith⟩)).scomp t
      ((hasDerivAt_id t).sub_const (n : ℝ))
    simp only [one_smul, hp] at hD
    exact hD.congr_of_eventuallyEq he

theorem schedule_material_flow {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) :
    MaterialFlow (scheduleVelocity v) (fun t a => repeatedPath v a t) ∧
      (∀ a, repeatedPath v a 1 = stageState v a m) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro a
    simpa only [Nat.cast_zero, periodState] using repeatedPath_at_nat v a 0
  · intro a t ht
    exact (repeatedPath_hasDerivAt v hv a ht).continuousAt.continuousWithinAt
  · intro a t ht
    exact (repeatedPath_hasDerivAt v hv a ht).hasDerivWithinAt
  · intro a
    simpa only [Nat.cast_one, periodState] using repeatedPath_at_nat v a 1

end Solenoidal

end

end OAI
