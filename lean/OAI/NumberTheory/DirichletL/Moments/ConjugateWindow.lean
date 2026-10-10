import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase (t u : ℝ) : star (logPhase t u)=logPhase (-t) u := by
  simp only [logPhase,Complex.star_def,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  push_cast
  ring

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

theorem conjugate_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (fun x => star (V x)) := by
  apply hV.comp_left
  simp

theorem conjugate_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => star (V x)) := by
  exact Complex.conjCLE.contDiff.comp hV

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI
