import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanOperator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryInversion

namespace OAI

/-! Exact energy and loss of the finite Kloosterman operator. The loss
is the Fourier energy outside the primary unit classes, with no analytic
estimate or local representation hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinResidueWeight_norm_sq (c : Eisenstein) (x : Residues (3*c)) :
    ‖cubicThetaEisensteinResidueWeight c x‖^2=
      if IsUnit x ∧ cubicThetaReductionThree c x=1 then 1 else 0 := by
  have he := congrArg Complex.re (cubicThetaEisensteinResidueWeight_square c x)
  simpa only [Complex.star_def,Complex.mul_conj',←Complex.ofReal_pow,
    Complex.ofReal_re,apply_ite,Complex.one_re,Complex.zero_re] using he

theorem cubicThetaWeightedResidueInversion_energy (c : Eisenstein)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (∑ x : Residues (3*c),‖cubicThetaWeightedResidueInversion c f x‖^2)=
      ∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then ‖f x‖^2 else 0 := by
  calc
    _ = ∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then
        ‖f (cubicThetaResidueInversePerm (3*c) x)‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [cubicThetaWeightedResidueInversion_perm,norm_mul,mul_pow,
        cubicThetaEisensteinResidueWeight_norm_sq]
      split_ifs <;> simp
    _ = ∑ x : Residues (3*c),if IsUnit (cubicThetaResidueInversePerm (3*c) x) ∧
        cubicThetaReductionThree c (cubicThetaResidueInversePerm (3*c) x)=1 then
        ‖f (cubicThetaResidueInversePerm (3*c) x)‖^2 else 0 := by
      simp only [cubicThetaPrimaryResidue_inverse_perm]
    _ = _ := (cubicThetaResidueInversePerm (3*c)).sum_comp
      (fun x : Residues (3*c) => if IsUnit x ∧ cubicThetaReductionThree c x=1 then ‖f x‖^2 else 0)

theorem cubicThetaFiniteKloostermanApply_energy (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (∑ h : Residues (3*c),‖cubicThetaFiniteKloostermanApply c hc0 f h‖^2)=
      (Fintype.card (Residues (3*c)):ℝ)*∑ x : Residues (3*c),
        if IsUnit x ∧ cubicThetaReductionThree c x=1 then
          ‖cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f x‖^2 else 0 := by
  simp_rw [cubicThetaFiniteKloostermanApply_factor]
  rw [cubicThetaFiniteFourier_norm_sq,cubicThetaWeightedResidueInversion_energy]

theorem cubicThetaFiniteKloostermanApply_loss (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (Fintype.card (Residues (3*c)):ℝ)^2*(∑ x : Residues (3*c),‖f x‖^2)-
        (∑ h : Residues (3*c),‖cubicThetaFiniteKloostermanApply c hc0 f h‖^2)=
      (Fintype.card (Residues (3*c)):ℝ)*∑ x : Residues (3*c),
        if IsUnit x ∧ cubicThetaReductionThree c x=1 then 0 else
          ‖cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f x‖^2 := by
  let F := cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f
  have he := cubicThetaFiniteFourier_norm_sq (3*c) (mul_ne_zero (by norm_num) hc0) f
  have hs : (∑ x : Residues (3*c),‖F x‖^2)=
      (∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then ‖F x‖^2 else 0)+
      (∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then 0 else ‖F x‖^2) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [cubicThetaFiniteKloostermanApply_energy]
  change _-(Fintype.card (Residues (3*c)):ℝ)*
    (∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then ‖F x‖^2 else 0)=_
  have hm := congrArg (fun y : ℝ => (Fintype.card (Residues (3*c)):ℝ)*y) he
  change (Fintype.card (Residues (3*c)):ℝ)*(∑ x : Residues (3*c),‖F x‖^2)=_ at hm
  rw [hs] at hm
  nlinarith [hm]

end CubicFirstMoment

end

end OAI
