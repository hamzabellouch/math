import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalPureCocycle

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K] (v : Kˣ)
def cocycleLift (c : ℤ → (RatFunc K)ˣ) (h0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u)) :
    Multiplicative ℤ →* PureExtension v where
  toFun t:=⟨c t.toAdd,t⟩
  map_one':=by apply SemidirectProduct.ext; exact h0; rfl
  map_mul' t u:=by apply SemidirectProduct.ext; exact hc _ _; rfl
lemma cocycle_eq_zpow (c : ℤ → (RatFunc K)ˣ) (h0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u)) (t : ℤ) :
    c t=((⟨c 1,Multiplicative.ofAdd 1⟩ : PureExtension v)^t).left := by
  have H:=map_zpow (cocycleLift v c h0 hc) (Multiplicative.ofAdd 1) t
  rw [←ofAdd_zsmul,smul_eq_mul,mul_one] at H
  exact congrArg SemidirectProduct.left H
lemma cocycle_ext (c d : ℤ → (RatFunc K)ˣ) (hc0 : c 0=1) (hd0 : d 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u))
    (hd : ∀t u,d (t+u)=d t*scaleAction v (Multiplicative.ofAdd t) (d u))
    (h1 : c 1=d 1) : c=d := by
  funext t
  rw [cocycle_eq_zpow v c hc0 hc,cocycle_eq_zpow v d hd0 hd,h1]
end
end ElementaryPositivity.RationalFiber

end

end OAI
