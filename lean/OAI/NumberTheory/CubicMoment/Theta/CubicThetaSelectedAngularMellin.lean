import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedAngularMellin

namespace OAI

/-! The inverse reciprocal law gives entire Mellin continuation for the
actual selected coefficients as well as for the projected dual family. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaLevelAngularRoot_ne_zero {q : Eisenstein} (hq : primary q)
    (rev : Bool) (k : ℕ) : cubicThetaLevelAngularRoot q rev k≠0 := by
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hN : (norm q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hq)).ne'
  have hd : -(norm q:ℂ)/(q:ℂ)^2≠0 := div_ne_zero (neg_ne_zero.mpr hN) (pow_ne_zero _ hqC)
  unfold cubicThetaLevelAngularRoot
  apply pow_ne_zero
  cases rev <;> simpa only [Bool.not_false,Bool.not_true,cubicThetaCircleMultiplier,
    Bool.false_eq_true,ite_false,ite_true,ne_eq,star_eq_zero] using hd

lemma cubicThetaSelectedAngularAxis_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicThetaSelectedAngularAxis g rev k (1/t)=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*(t:ℂ)^(2*k)*
        cubicThetaProjectedAngularAxis g hc rev k t := by
  have he := cubicThetaProjectedAngularAxis_functional g hc rev hk (inv_pos.mpr ht)
  simp only [one_div,inv_inv,Complex.ofReal_inv,inv_pow] at he
  have hr := cubicThetaLevelAngularRoot_ne_zero hc rev k
  have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [one_div]
  field_simp [hr,htC] at he ⊢
  exact he.symm

def cubicThetaSelectedAngularCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedAngularAxis g rev k)) s+
    (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
      mellin (thetaUpper (cubicThetaProjectedAngularAxis g hc rev k)) (((2*k:ℕ):ℂ)-s)

theorem cubicThetaSelectedAngular_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    MellinConvergent (cubicThetaSelectedAngularAxis g rev k) s ∧
      mellin (cubicThetaSelectedAngularAxis g rev k) s=
        cubicThetaSelectedAngularCompleted g hc rev k s := by
  apply theta_mellin_split_angular k
    (fun t ht => cubicThetaSelectedAngularAxis_functional g hc rev hk ht)
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) s
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) _

theorem cubicThetaSelectedAngularCompleted_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaSelectedAngularCompleted g hc rev k) := by
  have hf := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_arithmetic_bound (cubicThetaCircleOrder (!rev) k)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale_pos hc)
  have hg := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) (cubicThetaCircleOrder rev k)
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale_pos hc)
  have hlin : Differentiable ℂ (fun s : ℂ => ((2*k:ℕ):ℂ)-s) := by fun_prop
  exact hf.add ((hg.comp hlin).const_mul _)

theorem cubicThetaSelectedAngularCompleted_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    cubicThetaSelectedAngularCompleted g hc rev k s=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        cubicThetaProjectedAngularCompleted g hc rev k (((2*k:ℕ):ℂ)-s) := by
  rw [←(cubicThetaSelectedAngular_mellin g hc rev hk s).2,
    ←(cubicThetaProjectedAngular_mellin g hc rev hk _).2]
  exact theta_mellin_functional_angular k
    (fun t ht => cubicThetaSelectedAngularAxis_functional g hc rev hk ht) s

end CubicFirstMoment

end

end OAI
