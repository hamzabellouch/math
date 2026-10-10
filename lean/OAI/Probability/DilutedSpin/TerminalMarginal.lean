import OAI.Probability.DilutedSpin.CompoundRate

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

lemma expMoment_bind_one (P : FiniteLaw Ω) (Q : FiniteLaw A) (F : Ω×A → ℝ) :
    (P.bind (fun _ => Q)).expMoment 1 F =
      Q.expect (fun a => P.expMoment 1 (fun s => F (s,a))) := by
  unfold expMoment
  rw [expect_bind]
  simp only [one_mul,expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma logMean_bind_one_congr (P : FiniteLaw Ω) (R : FiniteLaw Λ) (Q : FiniteLaw A)
    (F : Ω×A → ℝ) (G : Λ×A → ℝ)
    (h : ∀ a, P.expMoment 1 (fun s => F (s,a)) = R.expMoment 1 (fun s => G (s,a))) :
    (P.bind (fun _ => Q)).logMean 1 F = (R.bind (fun _ => Q)).logMean 1 G := by
  simp only [logMean,div_one,expMoment_bind_one]
  rw [show (fun a => P.expMoment 1 (fun s => F (s,a))) =
    (fun a => R.expMoment 1 (fun s => G (s,a))) from funext h]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

/-- Equality of the genuine final-spin marginal propagates through every
auxiliary conditional power mean. The only required endpoint is m_L=1. -/
lemma terminal_marginal_congr (L : ℕ) (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (U : KernelTower A (L+1)) (m : Fin (L+1) → ℝ) (hm : m (Fin.last L)=1)
    (F : Ω → FinitePath A (L+1) → ℝ) (G : Λ → FinitePath A (L+1) → ℝ)
    (h : ∀ y, P.expMoment 1 (fun s => F s y) = R.expMoment 1 (fun s => G s y)) :
    backwardLog (L+1) (prod (L+1) (terminalTower a P L) U) m
      (fun y => F (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) =
    backwardLog (L+1) (prod (L+1) (terminalTower b R L) U) m
      (fun y => G (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) := by
  induction L with
  | zero =>
    change (P.bind (fun _ => U.1)).logMean (m 0) (fun z => F z.1 (z.2,())) =
      (R.bind (fun _ => U.1)).logMean (m 0) (fun z => G z.1 (z.2,()))
    change m 0=1 at hm
    rw [hm]
    exact FiniteLaw.logMean_bind_one_congr P R U.1 _ _ (fun u => h (u,()))
  | succ L ih =>
    change ( (FiniteLaw.point a).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower a P L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => F (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y))) =
      ((FiniteLaw.point b).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower b R L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => G (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y)))
    unfold FiniteLaw.logMean FiniteLaw.expMoment
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    simp only [FiniteLaw.expect_point]
    congr 1
    congr 1
    apply congrArg (FiniteLaw.expect U.1)
    funext u
    congr 1
    congr 1
    exact ih (U.2 u) (fun i => m i.succ) hm (fun s y => F s (u,y)) (fun s y => G s (u,y))
      (fun y => h (u,y))

end DilutedSpinGlass.KernelTower

end

end OAI
