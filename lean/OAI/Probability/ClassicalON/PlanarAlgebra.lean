import OAI.Probability.ClassicalON.TorusDouble

namespace OAI

universe uE uV

noncomputable section
namespace ClassicalON

open scoped ComplexConjugate

def planarCharacter (t : PlanarAngle) : ℂ := AddCircle.toCircle t

def planarCos (t : PlanarAngle) : ℝ := (planarCharacter t).re

def planarSin (t : PlanarAngle) : ℝ := (planarCharacter t).im

theorem continuous_planarCos : Continuous planarCos := by
  unfold planarCos planarCharacter
  exact Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem continuous_planarSin : Continuous planarSin := by
  unfold planarSin planarCharacter
  exact Complex.continuous_im.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem planarCharacter_add (x y : PlanarAngle) :
    planarCharacter (x+y)=planarCharacter x*planarCharacter y := by
  simp only [planarCharacter,AddCircle.toCircle_add,Circle.coe_mul]

theorem planarCharacter_neg (x : PlanarAngle) :
    planarCharacter (-x)=conj (planarCharacter x) := by
  simp only [planarCharacter,AddCircle.toCircle_neg,Circle.coe_inv_eq_conj]

theorem planarCos_add_sub (x y : PlanarAngle) :
    planarCos (x+y)+planarCos (x-y)=2*planarCos x*planarCos y := by
  simp only [planarCos,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem planarCos_subtraction (x y : PlanarAngle) :
    planarCos (x+y)-planarCos (x-y)= -2*planarSin x*planarSin y := by
  simp only [planarCos,planarSin,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

variable {V : Type uV} {E : Type uE}

def planarEnergy (left right : E → V) (e : E) (θ : V → PlanarAngle) : ℝ :=
  planarCos (θ (left e)-θ (right e))

def planarSine (left right : E → V) (e : E) (θ : V → PlanarAngle) : ℝ :=
  planarSin (θ (left e)-θ (right e))

theorem continuous_planarEnergy (left right : E → V) (e : E) :
    Continuous (planarEnergy left right e) := by
  exact continuous_planarCos.comp ((continuous_apply _).sub (continuous_apply _))

theorem continuous_planarSine (left right : E → V) (e : E) :
    Continuous (planarSine left right e) := by
  exact continuous_planarSin.comp ((continuous_apply _).sub (continuous_apply _))

theorem planarEnergy_double_sum (left right : E → V) (e : E)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarEnergy left right e (torusDouble p).1+planarEnergy left right e (torusDouble p).2=
      2*planarEnergy left right e p.1*planarEnergy left right e p.2 := by
  change planarCos ((p.1+p.2) (left e)-(p.1+p.2) (right e))+
    planarCos ((p.1-p.2) (left e)-(p.1-p.2) (right e))=_
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [show p.1 (left e)+p.2 (left e)-(p.1 (right e)+p.2 (right e))=
    (p.1 (left e)-p.1 (right e))+(p.2 (left e)-p.2 (right e)) by abel,
    show p.1 (left e)-p.2 (left e)-(p.1 (right e)-p.2 (right e))=
    (p.1 (left e)-p.1 (right e))-(p.2 (left e)-p.2 (right e)) by abel]
  exact planarCos_add_sub _ _

theorem planarEnergy_double_sub (left right : E → V) (e : E)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarEnergy left right e (torusDouble p).1-planarEnergy left right e (torusDouble p).2=
      -2*planarSine left right e p.1*planarSine left right e p.2 := by
  change planarCos ((p.1+p.2) (left e)-(p.1+p.2) (right e))-
    planarCos ((p.1-p.2) (left e)-(p.1-p.2) (right e))=_
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [show p.1 (left e)+p.2 (left e)-(p.1 (right e)+p.2 (right e))=
    (p.1 (left e)-p.1 (right e))+(p.2 (left e)-p.2 (right e)) by abel,
    show p.1 (left e)-p.2 (left e)-(p.1 (right e)-p.2 (right e))=
    (p.1 (left e)-p.1 (right e))-(p.2 (left e)-p.2 (right e)) by abel]
  exact planarCos_subtraction _ _

end ClassicalON

end

end OAI
