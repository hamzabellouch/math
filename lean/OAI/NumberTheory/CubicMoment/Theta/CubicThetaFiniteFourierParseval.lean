import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteConductor

namespace OAI

/-! Exact finite Fourier orthogonality and Parseval for the codifferent
pairing used by the Kloosterman row kernels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaResidueFourier_norm (q : Eisenstein) (hq : q≠0) (x : Residues q) :
    ‖residueFourierChar q hq x‖=1 := by
  change ‖(Real.fourierChar _:ℂ)‖=1
  exact Circle.norm_coe _

lemma cubicThetaResidueFourier_star (q : Eisenstein) (hq : q≠0) (x : Residues q) :
    star (residueFourierChar q hq x)=residueFourierChar q hq (-x) := by
  rw [AddChar.map_neg_eq_inv,Complex.inv_eq_conj (cubicThetaResidueFourier_norm q hq x)]
  rfl

lemma cubicThetaResidueFourier_orthogonal (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (x y : Residues q) :
    (∑ a : Residues q,residueFourierChar q hq (a*x)*star (residueFourierChar q hq (a*y)))=
      if x=y then (Fintype.card (Residues q):ℂ) else 0 := by
  classical
  have he (a : Residues q) : residueFourierChar q hq (a*x)*star (residueFourierChar q hq (a*y))=
      residueFourierChar q hq (a*(x-y)) := by
    rw [cubicThetaResidueFourier_star,←AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [AddChar.sum_mulShift (x-y) (residueFourierChar_isPrimitive q hq)]
  simp only [sub_eq_zero]
  split_ifs <;> simp

def cubicThetaFiniteFourier (q : Eisenstein) (hq : q≠0) [Fintype (Residues q)]
    (f : Residues q → ℂ) (a : Residues q) : ℂ :=
  ∑ x : Residues q,f x*residueFourierChar q hq (a*x)

lemma cubicThetaFiniteFourier_inverse_pairing (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (g : Residues q → ℂ) (x : Residues q) :
    (∑ a : Residues q,residueFourierChar q hq (a*x)*star (cubicThetaFiniteFourier q hq g a))=
      (Fintype.card (Residues q):ℂ)*star (g x) := by
  classical
  unfold cubicThetaFiniteFourier
  simp_rw [star_sum,star_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y : Residues q,star (g y)*
        ∑ a : Residues q,residueFourierChar q hq (a*x)*star (residueFourierChar q hq (a*y)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp only [cubicThetaResidueFourier_orthogonal]
      simp [mul_comm]

theorem cubicThetaFiniteFourier_parseval (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f g : Residues q → ℂ) :
    (∑ a : Residues q,cubicThetaFiniteFourier q hq f a*star (cubicThetaFiniteFourier q hq g a))=
      (Fintype.card (Residues q):ℂ)*∑ x : Residues q,f x*star (g x) := by
  classical
  conv_lhs => arg 2; ext a; arg 1; unfold cubicThetaFiniteFourier
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Residues q,f x*
        ∑ a : Residues q,residueFourierChar q hq (a*x)*star (cubicThetaFiniteFourier q hq g a) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp_rw [cubicThetaFiniteFourier_inverse_pairing]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

lemma cubicThetaFiniteFourier_norm_sq (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) :
    (∑ a : Residues q,‖cubicThetaFiniteFourier q hq f a‖^2)=
      (Fintype.card (Residues q):ℝ)*∑ x : Residues q,‖f x‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  have he := cubicThetaFiniteFourier_parseval q hq f f
  simpa only [Complex.star_def,Complex.mul_conj'] using he

end CubicFirstMoment

end

end OAI
