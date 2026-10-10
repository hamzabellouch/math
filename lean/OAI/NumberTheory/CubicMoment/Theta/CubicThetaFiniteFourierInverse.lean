import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteFourierParseval

namespace OAI

/-! The inverse of the actual finite codifferent Fourier transform,
including the cardinality normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaFiniteFourierAdjoint (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (x : Residues q) : ℂ :=
  ∑ a : Residues q,f a*star (residueFourierChar q hq (a*x))

lemma cubicThetaFiniteFourierAdjoint_conjugate (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourierAdjoint q hq f x=
      star (cubicThetaFiniteFourier q hq (fun a => star (f a)) x) := by
  unfold cubicThetaFiniteFourierAdjoint cubicThetaFiniteFourier
  simp only [star_sum,star_mul,star_star]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm a x]
  ring

theorem cubicThetaFiniteFourierAdjoint_inverse (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourierAdjoint q hq (cubicThetaFiniteFourier q hq f) x=
      (Fintype.card (Residues q):ℂ)*f x := by
  have he := congrArg star (cubicThetaFiniteFourier_inverse_pairing q hq f x)
  simpa only [star_sum,star_mul,star_star,star_natCast,mul_comm,
    cubicThetaFiniteFourierAdjoint] using he

theorem cubicThetaFiniteFourier_inverse_adjoint (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourier q hq (cubicThetaFiniteFourierAdjoint q hq f) x=
      (Fintype.card (Residues q):ℂ)*f x := by
  have he := congrArg star (cubicThetaFiniteFourierAdjoint_inverse q hq
    (fun a => star (f a)) x)
  simp only [cubicThetaFiniteFourierAdjoint_conjugate,star_star,star_mul,star_natCast] at he
  have ha : cubicThetaFiniteFourierAdjoint q hq f=
      fun a => star (cubicThetaFiniteFourier q hq (fun b => star (f b)) a) :=
    funext (cubicThetaFiniteFourierAdjoint_conjugate q hq f)
  rw [ha]
  exact he.trans (mul_comm _ _)

lemma cubicThetaFiniteFourier_const_mul (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (b : ℂ) (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourier q hq (fun a => b*f a) x=b*cubicThetaFiniteFourier q hq f x := by
  simp only [cubicThetaFiniteFourier,mul_assoc,Finset.mul_sum]

lemma cubicThetaFiniteFourierAdjoint_const_mul (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (b : ℂ) (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourierAdjoint q hq (fun a => b*f a) x=
      b*cubicThetaFiniteFourierAdjoint q hq f x := by
  simp only [cubicThetaFiniteFourierAdjoint,mul_assoc,Finset.mul_sum]

theorem cubicThetaFiniteFourier_injective (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] : Function.Injective (cubicThetaFiniteFourier q hq) := by
  intro f g hfg
  funext x
  have hn : (Fintype.card (Residues q):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Residues q))).ne'
  apply mul_left_cancel₀ hn
  rw [←cubicThetaFiniteFourierAdjoint_inverse q hq f x,
    ←cubicThetaFiniteFourierAdjoint_inverse q hq g x,hfg]

end CubicFirstMoment

end

end OAI
