import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.Torus
noncomputable section
variable {K M N : Type*} [CommRing K] [AddCommGroup M] [AddCommGroup N]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (Ω' : N →+ N →+ ℤ)
variable (L : M →+ N) (hL : ∀a b,Ω' (L a) (L b)=Ω a b)
def pushAdd : Torus v Ω →+ Torus v Ω' where
  toFun:=Finsupp.mapDomain L
  map_zero':=Finsupp.mapDomain_zero
  map_add' _ _:=Finsupp.mapDomain_add
@[simp] lemma pushAdd_monomial (m : M) (a : K) :
    pushAdd v Ω Ω' L (monomial v Ω m a)=monomial v Ω' (L m) a := Finsupp.mapDomain_single
include hL in
lemma pushAdd_mul (f g : Torus v Ω) :
    pushAdd v Ω Ω' L (f*g)=pushAdd v Ω Ω' L f*pushAdd v Ω Ω' L g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [add_mul,map_add,hf,hg]
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add f g hf hg=>simp only [mul_add,map_add,hf,hg]
    | single n b=>
      change pushAdd v Ω Ω' L (monomial v Ω m a*monomial v Ω n b)=
        pushAdd v Ω Ω' L (monomial v Ω m a)*pushAdd v Ω Ω' L (monomial v Ω n b)
      rw [monomial_mul_monomial,pushAdd_monomial,pushAdd_monomial,pushAdd_monomial,
        monomial_mul_monomial,hL,map_add]
def push : Torus v Ω →+* Torus v Ω' where
  __:=pushAdd v Ω Ω' L
  map_one':=by change pushAdd v Ω Ω' L (monomial v Ω 0 1)=monomial v Ω' 0 1; rw [pushAdd_monomial,map_zero]
  map_mul':=pushAdd_mul v Ω Ω' L hL
@[simp] lemma push_monomial (m : M) (a : K) :
    push v Ω Ω' L hL (monomial v Ω m a)=monomial v Ω' (L m) a := pushAdd_monomial v Ω Ω' L m a
@[simp] lemma push_X (m : M) : push v Ω Ω' L hL (X v Ω m)=X v Ω' (L m) := push_monomial v Ω Ω' L hL m 1
end
end ElementaryPositivity.QuantumTorus.Torus

end

end OAI
