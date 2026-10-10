import OAI.Probability.DilutedSpin.CavityEndpointCount
import OAI.Probability.DilutedSpin.FirstMomentFresh

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
lemma backwardLog_pi_terminal (a : ι → Ω) (P : ι → FiniteLaw Ω) (r : ℕ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,m d≠0) (f : (ι → Ω) → ℝ) :
    backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r)) m
      (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i)))=
      (FiniteLaw.pi P).logMean (m (Fin.last r)) f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (FiniteLaw.pi (fun i => FiniteLaw.point (a i))).logMean (m 0)
      (fun _ => backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r))
        (fun d => m d.succ) (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i))))=_
    rw [ih (fun d => m d.succ) (fun d => hm d.succ)]
    exact FiniteLaw.logMean_const _ (hm 0) _
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {p N : ℕ} [NeZero N]
omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_terminal (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (r : ℕ) (U : R → KernelTower Λ (r+1)) (x : R → FinitePath Λ (r+1) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1)
    (j : Fin p) (h : Fin N → ℝ) (k : ℕ) :
    upperCountMean M (KernelTower.pi (r+1) (fun _ : Fin N =>
      terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)) Q U
      (fun y s => terminalState r (FinitePath.proj (r+1) y s)) x m j
      (fun y => ∑ s,h s*spin (terminalState r (FinitePath.proj (r+1) y s))) k 0=
      ∫ z : Fin k → InteractionSample p,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
          (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  rw [upperCountMean_real_firstMoment M hM]
  · apply integral_congr_ae
    filter_upwards [] with z
    apply FiniteLaw.expect_congr
    intro i
    rw [backwardLog_pi_terminal (fun _ : Fin N => false)
      (fun _ => (FiniteLaw.uniform : FiniteLaw Spin)) r m (fun d => (hm d).ne')
      (fun σ => (∑ s,h s*spin (σ s))+∑ a,(z a).1 (fun b => σ (i a b))),hend,FiniteLaw.pi_uniform,
      FiniteLaw.logMean_uniform]
    unfold logPartition
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      unfold logWeight
      ring
    · simp [Real.log_pow]
  · exact hm
end DilutedSpinGlass.PrescribedTree

end

end OAI
