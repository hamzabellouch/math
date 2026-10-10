import OAI.Probability.DilutedSpin.TowerArraySplit

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma logMean_bind_point (P : FiniteLaw Ω) (a : Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    (P.bind (fun _ => point a)).logMean m f=P.logMean m (fun s => f (s,a)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
lemma logMean_point_bind (a : Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    ((point a).bind (fun _ => Q)).logMean m f=Q.logMean m (fun s => f (a,s)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_terminal_pad (a : Ω) (b : Λ) (P : FiniteLaw Ω)
    (r : ℕ) (U : KernelTower Λ r) (m : Fin (r+1) → ℝ) (F : Ω → FinitePath Λ r → ℝ) :
    backwardLog (r+1) (prod (r+1) (terminalTower a P r) (pad b r U)) m
      (fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y))) =
      backwardLog r U (fun d => m d.castSucc)
        (fun y => P.logMean (m (Fin.last r)) (fun s => F s y)) := by
  induction r with
  | zero =>
    change (P.bind (fun _ => FiniteLaw.point b)).logMean (m 0) (fun z => F z.1 ()) =
      P.logMean (m (Fin.last 0)) (fun s => F s ())
    exact FiniteLaw.logMean_bind_point P b _ _
  | succ r ih =>
    simp only [backwardLog,prod,terminalTower,pad,pathFst,pathSnd,terminalState,pathPrefix]
    rw [FiniteLaw.logMean_point_bind]
    apply congrArg (U.1.logMean (m 0))
    funext z
    exact ih (U.2 z) (fun d => m d.succ) (fun s y => F s (z,y))

end DilutedSpinGlass.KernelTower

end

end OAI
