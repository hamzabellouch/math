import OAI.Analysis.WeakInfiniteness.RectangularCStar
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit

namespace OAI

/-! Algebraic identities with the rectangular CStarMatrix type kept explicit. -/

namespace WeakPureInfiniteness

variable {A I J K L : Type*} [NonUnitalRing A]

lemma rectangular_conjTranspose_mul [StarRing A] [Fintype J]
    (a : CStarMatrix I J A) (b : CStarMatrix J K A) :
    (a * b).conjTranspose = b.conjTranspose * a.conjTranspose := Matrix.conjTranspose_mul a b

lemma rectangular_mul_one {B : Type*} [Ring B] [Fintype J] [DecidableEq J]
    (a : CStarMatrix I J B) : a * (1 : CStarMatrix J J B) = a := Matrix.mul_one a

end WeakPureInfiniteness

end OAI
