import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroObservable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTent
import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth

namespace OAI

/-! The constant-mode radial factor is an entire compact Mellin transform. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaRadialTestWeight_star (v : ℝ) :
    star (cubicThetaRadialTestWeight v)=cubicThetaRadialTestWeight v := by
  simp [cubicThetaRadialTestWeight_apply]

lemma cubicThetaRadialTestWeight_zero {v : ℝ} (hv : v≤2) :
    cubicThetaRadialTestWeight v=0 := by
  rw [cubicThetaRadialTestWeight_apply]
  have ha : 1≤|v-3| := by
    rw [abs_of_nonpos (by linarith : v-3≤0)]
    linarith
  simp only [cubicThetaRadialTent,max_eq_left (by linarith : 1-|v-3|≤0),Complex.ofReal_zero]

lemma cubicThetaRadialTestWeight_tsupport :
    tsupport cubicThetaRadialTestWeight⊆Icc (2:ℝ) 4 := by
  apply closure_minimal ?_ isClosed_Icc
  intro v hv
  have hn : cubicThetaRadialTent v≠0 := by
    intro hz
    exact hv (by rw [cubicThetaRadialTestWeight_apply,hz,Complex.ofReal_zero])
  have hp : 0<1-|v-3| := by
    by_contra hh
    exact hn (max_eq_left (le_of_not_gt hh))
  have h := abs_lt.mp (show |v-3|<1 by linarith)
  constructor <;> linarith

theorem cubicThetaZeroRadialTest_mellin (s : ℂ) :
    cubicThetaZeroRadialTest cubicThetaRadialTestWeight s=
      mellin cubicThetaRadialTestWeight (-s) := by
  have he : (∫ v in Ioi (2:ℝ), star (cubicThetaRadialTestWeight v)*(v:ℂ)^(2-s)/(v:ℂ)^3)=
      ∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*cubicThetaRadialTestWeight v := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    change 2<v at hv
    dsimp only
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hp : (v:ℂ)^(2-s)/(v:ℂ)^3=(v:ℂ)^(-s-1) := by
      rw [← Complex.cpow_natCast,← Complex.cpow_sub _ _ hv0]
      congr 1
      norm_num
      ring
    rw [cubicThetaRadialTestWeight_star]
    calc
      _ = ((v:ℂ)^(2-s)/(v:ℂ)^3)*cubicThetaRadialTestWeight v := by ring
      _ = _ := by rw [hp]
  unfold cubicThetaZeroRadialTest
  rw [he]
  have h₂ : (∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*cubicThetaRadialTestWeight v)=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*cubicThetaRadialTestWeight v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [cubicThetaRadialTestWeight_zero (le_of_not_gt hv),mul_zero]
  have h₀ : (∫ v in Ioi (0:ℝ), (v:ℂ)^(-s-1)*cubicThetaRadialTestWeight v)=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*cubicThetaRadialTestWeight v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [cubicThetaRadialTestWeight_zero (le_trans (le_of_not_gt hv) (by norm_num)),mul_zero]
  rw [h₂,← h₀]
  rfl

theorem cubicThetaZeroRadialTest_entire :
    Differentiable ℂ (cubicThetaZeroRadialTest cubicThetaRadialTestWeight) := by
  have hp : tsupport cubicThetaRadialTestWeight⊆Ioi (0:ℝ) := by
    intro v hv
    exact lt_of_lt_of_le (by norm_num) (cubicThetaRadialTestWeight_tsupport hv).1
  have hm := smooth_mellin_entire cubicThetaRadialTestWeight
    cubicThetaRadialTestWeight.hasCompactSupport hp cubicThetaRadialTestWeight.continuous
  have he : cubicThetaZeroRadialTest cubicThetaRadialTestWeight=
      (fun s : ℂ => mellin cubicThetaRadialTestWeight (-s)) :=
    funext cubicThetaZeroRadialTest_mellin
  rw [he]
  exact hm.comp differentiable_id.neg

end CubicFirstMoment

end

end OAI
