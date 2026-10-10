import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalFiberTorus

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

def embeddedMonomial (m : M) : K →+
    FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) where
  toFun a:=FiberTorus.monomial v _ _ (off k p hp m)
    (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m)))
  map_zero':=by simp
  map_add' a b:=by simp [add_mul]
def embedAdd : Torus v Ω →+
    FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) :=
  Finsupp.liftAddHom (embeddedMonomial v Ω k p hp)
@[simp] lemma embedAdd_monomial (m : M) (a : K) :
    embedAdd v Ω k p hp (Torus.monomial v Ω m a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m))) :=
  Finsupp.liftAddHom_apply_single _ _ _
include hΩ in
lemma embeddedMonomial_mul (m n : M) (a b : K) :
    embedAdd v Ω k p hp (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      embedAdd v Ω k p hp (Torus.monomial v Ω m a)*
      embedAdd v Ω k p hp (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,embedAdd_monomial,embedAdd_monomial,embedAdd_monomial,
    FiberTorus.monomial_mul]
  simp only [map_add]
  congr 1
  simp only [map_mul,FiberTorus.twist_constant]
  let am:=complementAlpha k p Ω (off k p hp m)
  let an:=complementAlpha k p Ω (off k p hp n)
  let c:=complementOmega k Ω (off k p hp m) (off k p hp n)
  change RatFunc.C a*RatFunc.C b*RatFunc.C (↑(v^(Ω m n)):K)*
    centeredScalar v (k m+k n) (am+an)=
    (RatFunc.C a*centeredScalar v (k m) am)*
      (RatFunc.C b*scale (v^(-2*am)) (centeredScalar v (k n) an))*RatFunc.C (↑(v^c):K)
  have H:=centeredScalar_mul v (k m) (k n) am an c
  rw [←split_pairing k p hp Ω hΩ m n] at H
  calc
    _ = RatFunc.C a*RatFunc.C b*(RatFunc.C (↑(v^(Ω m n)):K)*
      centeredScalar v (k m+k n) (am+an)) := by ring
    _ = RatFunc.C a*RatFunc.C b*(centeredScalar v (k m) am*
      scale (v^(-2*am)) (centeredScalar v (k n) an)*RatFunc.C (↑(v^c):K)) := by rw [H]
    _ = _ := by ring
include hΩ in
lemma embedAdd_mul (f g : Torus v Ω) :
    embedAdd v Ω k p hp (f*g)=embedAdd v Ω k p hp f*embedAdd v Ω k p hp g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,map_add,hg,hg']
    | single n b=>exact embeddedMonomial_mul v Ω hΩ k p hp m n a b
lemma embedAdd_one : embedAdd v Ω k p hp 1=1 := by
  change embedAdd v Ω k p hp (Torus.monomial v Ω 0 1)=FiberTorus.monomial v _ _ 0 1
  simp [embedAdd_monomial,centeredScalar]
def embed : Torus v Ω →+* FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) where
  __:=embedAdd v Ω k p hp
  map_one':=embedAdd_one v Ω k p hp
  map_mul':=embedAdd_mul v Ω hΩ k p hp
@[simp] lemma embed_monomial (m : M) (a : K) :
    embed v Ω hΩ k p hp (Torus.monomial v Ω m a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m))) :=
  embedAdd_monomial v Ω k p hp m a
@[simp] lemma embed_p : embed v Ω hΩ k p hp (Torus.X v Ω p)=
    FiberTorus.coefficient v _ _ RatFunc.X := by
  simp [Torus.X,embed_monomial,hp,centeredScalar,FiberTorus.coefficient]
@[simp] lemma embed_complement (m : k.ker) :
    embed v Ω hΩ k p hp (Torus.X v Ω m)=FiberTorus.X v _ _ m := by
  have hm : k m=0:=m.property
  simp [Torus.X,embed_monomial,hm,centeredScalar,FiberTorus.X]
end
end ElementaryPositivity.RationalFiber

end

end OAI
