import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusEmbedding
import OAI.Combinatorics.Chromatic.Walls.RationalFiberReciprocal

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma expand_centeredScalar (n a : ℤ) (b : K) :
    expandZero (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single n (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandZero_constant,expandZero_X_zpow]
  simp [HahnSeries.C]

def readFiber (m : M) : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+ K where
  toFun f:=(expandZero (f (off k p hp m))).coeff (k m)*
    (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  map_zero':=by simp
  map_add' f g:=by simp [add_mul]
lemma split_injective {m n : M} (hk : k m=k n) (ho : off k p hp m=off k p hp n) : m=n := by
  rw [←split_sum k p hp m,←split_sum k p hp n,hk,ho]
lemma readFiber_monomial (m n : M) (a : K) :
    readFiber v Ω k p hp m (embedAdd v Ω k p hp (Torus.monomial v Ω n a))=
      (Torus.monomial v Ω n a) m := by
  classical
  rw [embedAdd_monomial]
  change (expandZero ((Finsupp.single (off k p hp n)
    (RatFunc.C a*centeredScalar v (k n) (complementAlpha k p Ω (off k p hp n))))
    (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=Finsupp.single n a m
  by_cases ho : off k p hp n=off k p hp m
  · rw [Finsupp.single_apply,ite_eq_left ho,expand_centeredScalar]
    by_cases hk : k n=k m
    · have hn : n=m:=split_injective k p hp hk ho
      subst n
      rw [HahnSeries.coeff_single,ite_eq_left rfl,Finsupp.single_eq_same]
      rw [mul_assoc,←Units.val_mul,←zpow_add]
      simp
    · have hn : n≠m:=fun h=>hk (congrArg k h)
      simp [Ne.symm hk,Finsupp.single_eq_of_ne (Ne.symm hn)]
  · have hn : n≠m:=fun h=>ho (congrArg (off k p hp) h)
    rw [Finsupp.single_apply,ite_eq_right ho]
    simp [Finsupp.single_eq_of_ne (Ne.symm hn)]
lemma readFiber_embedAdd (f : Torus v Ω) (m : M) :
    readFiber v Ω k p hp m (embedAdd v Ω k p hp f)=f m := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp [map_add,hf,hg]
  | single n a=>exact readFiber_monomial v Ω k p hp m n a
lemma embed_injective : Function.Injective (embed v Ω hΩ k p hp) := by
  intro f g h
  ext m
  have H:=congrArg (readFiber v Ω k p hp m) h
  change readFiber v Ω k p hp m (embedAdd v Ω k p hp f)=
    readFiber v Ω k p hp m (embedAdd v Ω k p hp g) at H
  simpa only [readFiber_embedAdd] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
