import OAI.Analysis.LipschitzHilbert.Estimates.StoppedMartingaleChain
import Mathlib.Probability.Process.HittingTime

namespace OAI

/-! Actual successive exits from a fixed-radius ball around the previous
stopped value. All times stay inside the prescribed finite horizon. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}

def nextMartingaleExit (F : ℕ → Ω → ℝ) (lambda : ℝ) (N : ℕ) (σ : Ω → ℕ) : Ω → ℕ :=
  hittingBtwn (fun n x => ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖)
    (Ioi lambda) 0 N

omit m in
theorem nextMartingaleExit_le (F : ℕ → Ω → ℝ) (lambda : ℝ) (N : ℕ) (σ : Ω → ℕ) (x : Ω) :
    nextMartingaleExit F lambda N σ x≤N := hittingBtwn_le x

theorem nextMartingaleExit_isStopping (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F)
    (lambda : ℝ) (N : ℕ) (σ : Ω → ℕ)
    (hσ : IsStoppingTime ℱ (fun x => (σ x:WithTop ℕ))) :
    IsStoppingTime ℱ (fun x => (nextMartingaleExit F lambda N σ x:WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn (s:=Ioi lambda) _ measurableSet_Ioi
  intro n
  have hs := hF.isStronglyProgressive_of_discrete.stronglyAdapted_stoppedProcess hσ n
  exact ((hF n).sub hs).norm.measurable

omit m in
theorem nextMartingaleExit_ge (F : ℕ → Ω → ℝ) (lambda : ℝ) (hlambda : 0≤lambda)
    (N : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤N) (x : Ω) :
    σ x≤nextMartingaleExit F lambda N σ x := by
  by_contra hn
  have hlt : nextMartingaleExit F lambda N σ x<σ x := lt_of_not_ge hn
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt (hlt.trans_le (hσ x))
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (nextMartingaleExit F lambda N σ x) x=F (nextMartingaleExit F lambda N σ x) x := by
    unfold stoppedProcess
    rw [min_eq_left (by change (nextMartingaleExit F lambda N σ x:WithTop ℕ)≤(σ x:WithTop ℕ); exact_mod_cast hlt.le)]
    rfl
  change lambda<‖F (nextMartingaleExit F lambda N σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (nextMartingaleExit F lambda N σ x) x‖ at hh
  rw [he,sub_self,norm_zero] at hh
  linarith

omit m in
theorem nextMartingaleExit_before (F : ℕ → Ω → ℝ) (lambda : ℝ) (N : ℕ)
    (σ : Ω → ℕ) (x : Ω) (k : ℕ) (hσk : σ x≤k)
    (hk : k<nextMartingaleExit F lambda N σ x) : ‖F k x-F (σ x) x‖≤lambda := by
  have hh := notMem_of_lt_hittingBtwn (u:=fun n x =>
    ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖)
    (s:=Ioi lambda) hk (Nat.zero_le k)
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(k:WithTop ℕ); exact_mod_cast hσk)]
    rfl
  exact le_of_not_gt (by simpa only [mem_Ioi,he] using hh)

def martingaleExitTimes (F : ℕ → Ω → ℝ) (lambda : ℝ) (N : ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | i+1 => nextMartingaleExit F lambda N (martingaleExitTimes F lambda N i)

omit m in
theorem martingaleExitTimes_le (F : ℕ → Ω → ℝ) (lambda : ℝ) (N i : ℕ) (x : Ω) :
    martingaleExitTimes F lambda N i x≤N := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact nextMartingaleExit_le F lambda N _ x

theorem martingaleExitTimes_isStopping (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F)
    (lambda : ℝ) (N i : ℕ) :
    IsStoppingTime ℱ (fun x => (martingaleExitTimes F lambda N i x:WithTop ℕ)) := by
  induction i with
  | zero => exact isStoppingTime_const ℱ 0
  | succ i ih => exact nextMartingaleExit_isStopping F hF lambda N _ ih

omit m in
theorem martingaleExitTimes_mono (F : ℕ → Ω → ℝ) (lambda : ℝ) (hlambda : 0≤lambda)
    (N i : ℕ) (x : Ω) : martingaleExitTimes F lambda N i x≤martingaleExitTimes F lambda N (i+1) x :=
  nextMartingaleExit_ge F lambda hlambda N _ (martingaleExitTimes_le F lambda N i) x

omit m in
theorem nextMartingaleExit_jump (F : ℕ → Ω → ℝ) (lambda : ℝ) (hlambda : 0≤lambda)
    (N : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤N) (x : Ω)
    (hlt : nextMartingaleExit F lambda N σ x<N) :
    lambda<‖F (nextMartingaleExit F lambda N σ x) x-F (σ x) x‖ := by
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  have hle := nextMartingaleExit_ge F lambda hlambda N σ hσ x
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (nextMartingaleExit F lambda N σ x) x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(nextMartingaleExit F lambda N σ x:WithTop ℕ); exact_mod_cast hle)]
    rfl
  change lambda<‖F (nextMartingaleExit F lambda N σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (nextMartingaleExit F lambda N σ x) x‖ at hh
  rwa [he] at hh

omit m in
theorem martingaleExitTimes_min_le (F : ℕ → Ω → ℝ) (lambda : ℝ) (hlambda : 0≤lambda)
    (N i : ℕ) (x : Ω) : min i N≤martingaleExitTimes F lambda N i x := by
  induction i with
  | zero => simp [martingaleExitTimes]
  | succ i ih =>
    have hb := martingaleExitTimes_le F lambda N (i+1) x
    by_cases hlt : martingaleExitTimes F lambda N (i+1) x<N
    · have hj := nextMartingaleExit_jump F lambda hlambda N
        (martingaleExitTimes F lambda N i) (martingaleExitTimes_le F lambda N i) x hlt
      have hm := martingaleExitTimes_mono F lambda hlambda N i x
      have hn : martingaleExitTimes F lambda N i x≠martingaleExitTimes F lambda N (i+1) x := by
        intro he
        change lambda<‖F (martingaleExitTimes F lambda N (i+1) x) x-
          F (martingaleExitTimes F lambda N i x) x‖ at hj
        rw [he,sub_self,norm_zero] at hj
        linarith
      omega
    · omega

omit m in
theorem martingaleExitTimes_terminal (F : ℕ → Ω → ℝ) (lambda : ℝ) (hlambda : 0≤lambda)
    (N : ℕ) (x : Ω) : martingaleExitTimes F lambda N N x=N := by
  exact Nat.le_antisymm (martingaleExitTimes_le F lambda N N x)
    (by simpa using martingaleExitTimes_min_le F lambda hlambda N N x)

theorem martingaleExitTimes_jump_energy {μ : Measure Ω} [IsFiniteMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (lambda : ℝ) (hlambda : 0≤lambda) (N J : ℕ) :
    lambda^2*(∫ x, ∑ i∈Finset.range J,
      if lambda≤|F (martingaleExitTimes F lambda N (i+1) x) x-
        F (martingaleExitTimes F lambda N i x) x| then (1:ℝ) else 0 ∂μ)≤∫ x, F N x^2 ∂μ := by
  let τ := fun i x => (martingaleExitTimes F lambda N i x:WithTop ℕ)
  have hτ (i : ℕ) : IsStoppingTime ℱ (τ i) := martingaleExitTimes_isStopping F hF.1 lambda N i
  have hm (i : ℕ) : τ i≤τ (i+1) := fun x => by
    change (martingaleExitTimes F lambda N i x:WithTop ℕ)≤
      (martingaleExitTimes F lambda N (i+1) x:WithTop ℕ)
    exact_mod_cast martingaleExitTimes_mono F lambda hlambda N i x
  have hb (i : ℕ) (x : Ω) : τ i x≤N := by
    change (martingaleExitTimes F lambda N i x:WithTop ℕ)≤(N:WithTop ℕ)
    exact_mod_cast martingaleExitTimes_le F lambda N i x
  exact stoppedJumpCount_energy hF hF2 τ hτ hm N J hb lambda hlambda

end LipschitzHilbert

end

end OAI
