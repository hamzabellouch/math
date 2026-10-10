import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngularReciprocity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelInverse
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplitAngular

namespace OAI

/-! Entire Mellin continuation of the actual nonzero angular series at inverse cusps. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaLevelAngularPhase (q x : Eisenstein) (rev : Bool) (k : ℕ) : ℂ :=
  cubicSymbol q (3*x)*cubicThetaLevelAngularRoot q rev k

lemma cubicThetaLevelAngularAxis_functional {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
      (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q) (1/t)=
    cubicThetaLevelAngularPhase q x rev k*(t:ℂ)^(2*k)*
      cubicThetaScaledAngularAxis (cubicThetaCircleOrder (!rev) k)
        (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q) t := by
  have H := cubicThetaLevelAngularAxis_reciprocity hq x y hxy rev hk ht
  have hχ := cubicThetaLevel_inverse_phases hq hxy
  calc
    _ = cubicSymbol q (3*x)*(cubicSymbol q (3*y)*
        cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
          (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q) (1/t)) := by
      rw [←mul_assoc,hχ,one_mul]
    _ = _ := by rw [H]; unfold cubicThetaLevelAngularPhase; ring

def cubicThetaLevelAngularCompleted (q x y : Eisenstein) (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
      (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q))) s+
    cubicThetaLevelAngularPhase q x rev k*
      mellin (thetaUpper (cubicThetaScaledAngularAxis (cubicThetaCircleOrder (!rev) k)
        (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q))) (((2*k:ℕ):ℂ)-s)

theorem cubicThetaLevelAngular_mellin {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    MellinConvergent (cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
        (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q)) s ∧
    mellin (cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
        (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q)) s=
      cubicThetaLevelAngularCompleted q x y rev k s := by
  exact theta_mellin_split_angular k (fun t ht =>
    cubicThetaLevelAngularAxis_functional hq x y hxy rev hk ht)
    (cubicThetaScaledAngularUpper_mellinConvergent _ _ (cubicThetaLevelScale_pos hq) s)
    (cubicThetaScaledAngularUpper_mellinConvergent _ _ (cubicThetaLevelScale_pos hq) _)

theorem cubicThetaLevelAngularCompleted_entire {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaLevelAngularCompleted q x y rev k) := by
  have hf := cubicThetaScaledAngularUpper_entire (cubicThetaCircleOrder rev k)
    (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale_pos hq)
  have hg := cubicThetaScaledAngularUpper_entire (cubicThetaCircleOrder (!rev) k)
    (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale_pos hq)
  have hlin : Differentiable ℂ (fun s : ℂ => ((2*k:ℕ):ℂ)-s) := by fun_prop
  exact hf.add ((hg.comp hlin).const_mul _)

end CubicFirstMoment

end

end OAI
