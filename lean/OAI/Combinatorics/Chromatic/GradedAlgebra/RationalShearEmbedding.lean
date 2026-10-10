import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalCenteredAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma centeredScalar_shear (n t : ℤ) :
    centeredScalar v (n-t) t=centeredScalar v n t*(shearRatio v t:RatFunc K) := by
  rw [shearRatio_val,centeredScalar,centeredScalar]
  rw [show -(n-t)*t= -n*t+t*t by ring,zpow_add,Units.val_mul,map_mul,
    sub_eq_add_neg,zpow_add₀ RatFunc.X_ne_zero]
  ring
include hΩ in
lemma shearAction_embed_monomial (m : M) (a : K) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.monomial v Ω m a))=
      embed v Ω hΩ k p hp (Torus.monomial v Ω (mutationShear Ω p m) a) := by
  rw [embed_monomial,embed_monomial]
  change FiberTorus.gauge v _ _ _ _ _ (FiberTorus.monomial v _ _ _ _)=_
  rw [FiberTorus.gauge_monomial]
  have Hoff : off k p hp (mutationShear Ω p m)=off k p hp m := by
    change off k p hp (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,off_p,smul_zero,sub_zero]
  have Hk : k (mutationShear Ω p m)=k m-Ω p m := by
    change k (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,hp,smul_eq_mul,mul_one]
  rw [Hoff,Hk,complement_pairing Ω hΩ k p hp m,centeredScalar_shear]
  rw [mul_assoc]
include hΩ in
lemma shearAction_embed (f : Torus v Ω) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp f)=
      embed v Ω hΩ k p hp
        (Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change _=embed v Ω hΩ k p hp (Torus.push v Ω Ω _ _ (Torus.monomial v Ω m a))
    rw [Torus.push_monomial]
    exact shearAction_embed_monomial v Ω hΩ k p hp m a
end
end ElementaryPositivity.RationalFiber

end

end OAI
