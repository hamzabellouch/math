import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleExitTimes

namespace OAI

/-! Relative exits for the finite scalar specialization of Zorin-Kranich,
Bernoulli 26 (2020), Definition 2.1. The running radius is measured from
the initial value; the terminal time is one step beyond the path in use. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

variable {Ω : Type*}

def runningOscillation (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  finiteMaxSignal (fun k y => F k y-F 0 y) n x

theorem runningOscillation_nonneg (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) :
    0≤runningOscillation F n x := finiteMaxSignal_nonneg _ _ _

theorem le_runningOscillation (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    ‖F k x-F 0 x‖≤runningOscillation F n x := by
  simpa only [runningOscillation,finiteMaxSignal,Real.norm_eq_abs] using
    (Finset.le_sup' (fun i => |F i x-F 0 x|) (show k∈Finset.range (n+1) by simp; omega))

theorem runningOscillation_le (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) (A : ℝ)
    (h : ∀ k≤n, ‖F k x-F 0 x‖≤A) : runningOscillation F n x≤A := by
  unfold runningOscillation finiteMaxSignal
  apply Finset.sup'_le _
  intro k hk
  exact (Real.norm_eq_abs _).symm.trans_le (h k (by simpa using hk))

theorem runningOscillation_mono (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    runningOscillation F k x≤runningOscillation F n x :=
  runningOscillation_le F k x _ (fun _ hi => le_runningOscillation F (hi.trans h) x)

theorem runningOscillation_adapted [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) : Adapted ℱ (runningOscillation F) := by
  intro n
  change @Measurable Ω ℝ (ℱ n) _ (finiteMaxSignal (fun k y => F k y-F 0 y) n)
  apply @finiteMaxSignal_measurable Ω (ℱ n) (fun k y => F k y-F 0 y) n
  intro i hi
  exact (((hF i).mono (ℱ.mono hi)).sub ((hF 0).mono (ℱ.mono (Nat.zero_le n)))).measurable

def relativeNextExit (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (σ : Ω → ℕ) : Ω → ℕ :=
  hittingBtwn (fun n x => ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖-
    a*runningOscillation F n x) (Ioi 0) 0 H

theorem relativeNextExit_le (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (σ : Ω → ℕ) (x : Ω) :
    relativeNextExit F a H σ x≤H := hittingBtwn_le x

theorem relativeNextExit_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) (σ : Ω → ℕ)
    (hσ : IsStoppingTime ℱ (fun x => (σ x:WithTop ℕ))) :
    IsStoppingTime ℱ (fun x => (relativeNextExit F a H σ x:WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn (s:=Ioi 0) _ measurableSet_Ioi
  intro n
  have hs := hF.isStronglyProgressive_of_discrete.stronglyAdapted_stoppedProcess hσ n
  exact (((hF n).sub hs).norm.measurable).sub ((runningOscillation_adapted F hF n).const_mul a)

theorem relativeNextExit_ge (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω) :
    σ x≤relativeNextExit F a H σ x := by
  by_contra hn
  have hlt : relativeNextExit F a H σ x<σ x := lt_of_not_ge hn
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt (hlt.trans_le (hσ x))
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (relativeNextExit F a H σ x) x := by
    unfold stoppedProcess
    rw [min_eq_left (by change (relativeNextExit F a H σ x:WithTop ℕ)≤(σ x:WithTop ℕ); exact_mod_cast hlt.le)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he,sub_self,norm_zero] at hh
  have := mul_nonneg ha (runningOscillation_nonneg F (relativeNextExit F a H σ x) x)
  linarith

theorem relativeNextExit_before (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ)
    (σ : Ω → ℕ) (x : Ω) (k : ℕ) (hσk : σ x≤k)
    (hk : k<relativeNextExit F a H σ x) :
    ‖F k x-F (σ x) x‖≤a*runningOscillation F k x := by
  have hh := notMem_of_lt_hittingBtwn (u:=fun n x =>
    ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖-
      a*runningOscillation F n x) (s:=Ioi 0) hk (Nat.zero_le k)
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(k:WithTop ℕ); exact_mod_cast hσk)]
    rfl
  change ¬0<‖F k x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x‖-
    a*runningOscillation F k x at hh
  rw [he] at hh
  linarith

theorem relativeNextExit_jump (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω)
    (hlt : relativeNextExit F a H σ x<H) :
    a*runningOscillation F (relativeNextExit F a H σ x) x<
      ‖F (relativeNextExit F a H σ x) x-F (σ x) x‖ := by
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  have hle := relativeNextExit_ge F a ha H σ hσ x
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(relativeNextExit F a H σ x:WithTop ℕ); exact_mod_cast hle)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he] at hh
  linarith

def relativeExitTimes (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | i+1 => relativeNextExit F a H (relativeExitTimes F a H i)

theorem relativeExitTimes_le (F : ℕ → Ω → ℝ) (a : ℝ) (H i : ℕ) (x : Ω) :
    relativeExitTimes F a H i x≤H := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact relativeNextExit_le F a H _ x

theorem relativeExitTimes_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H i : ℕ) :
    IsStoppingTime ℱ (fun x => (relativeExitTimes F a H i x:WithTop ℕ)) := by
  induction i with
  | zero => exact isStoppingTime_const ℱ 0
  | succ i ih => exact relativeNextExit_isStopping F hF a H _ ih

theorem relativeExitTimes_mono (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : Monotone (fun i => relativeExitTimes F a H i x) := by
  apply monotone_nat_of_le_succ
  intro i
  exact relativeNextExit_ge F a ha H _ (relativeExitTimes_le F a H i) x

theorem relativeExitTimes_min_le (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H i : ℕ) (x : Ω) : min i H≤relativeExitTimes F a H i x := by
  induction i with
  | zero => simp [relativeExitTimes]
  | succ i ih =>
    have hb := relativeExitTimes_le F a H (i+1) x
    by_cases hlt : relativeExitTimes F a H (i+1) x<H
    · have hj := relativeNextExit_jump F a ha H
        (relativeExitTimes F a H i) (relativeExitTimes_le F a H i) x hlt
      have hm : relativeExitTimes F a H i x≤relativeExitTimes F a H (i+1) x :=
        relativeExitTimes_mono F a ha H x (Nat.le_succ i)
      have hn : relativeExitTimes F a H i x≠relativeExitTimes F a H (i+1) x := by
        intro he
        change a*runningOscillation F (relativeExitTimes F a H (i+1) x) x<
          ‖F (relativeExitTimes F a H (i+1) x) x-F (relativeExitTimes F a H i x) x‖ at hj
        rw [he,sub_self,norm_zero] at hj
        have := mul_nonneg ha (runningOscillation_nonneg F (relativeExitTimes F a H (i+1) x) x)
        linarith
      omega
    · omega

theorem relativeExitTimes_terminal (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : relativeExitTimes F a H H x=H := by
  exact Nat.le_antisymm (relativeExitTimes_le F a H H x)
    (by simpa using relativeExitTimes_min_le F a ha H H x)

end LipschitzHilbert

end

end OAI
