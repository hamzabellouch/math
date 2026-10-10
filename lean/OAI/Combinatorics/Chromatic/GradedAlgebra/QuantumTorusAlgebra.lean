import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus.Torus
noncomputable section
variable {S R M : Type*} [CommSemiring S] [CommRing R] [Algebra S R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

lemma scalar_one (r : S) : r • (1 : Torus v Ω)=monomial v Ω 0 (r • (1:R)) := by
  change r • Finsupp.single 0 (1:R)=Finsupp.single 0 (r • (1:R))
  exact Finsupp.smul_single _ _ _

lemma scalar_one_mul (r : S) (f : Torus v Ω) :
    (r • (1 : Torus v Ω))*f=r • f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add,hf,hg,smul_add]
  | single m a =>
    change (r • (1 : Torus v Ω))*monomial v Ω m a=r • monomial v Ω m a
    rw [scalar_one,monomial_mul_monomial]
    simp only [map_zero,AddMonoidHom.zero_apply,zpow_zero,Units.val_one,zero_add,_root_.mul_one,
      smul_mul_assoc,_root_.one_mul,monomial,Finsupp.smul_single]

lemma mul_scalar_one (r : S) (f : Torus v Ω) :
    f*(r • (1 : Torus v Ω))=r • f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul,hf,hg,smul_add]
  | single m a =>
    change monomial v Ω m a*(r • (1 : Torus v Ω))=r • monomial v Ω m a
    rw [scalar_one,monomial_mul_monomial]
    simp only [map_zero,zpow_zero,Units.val_one,add_zero,_root_.mul_one,
      mul_smul_comm,_root_.mul_one,monomial,Finsupp.smul_single]

instance : Algebra S (Torus v Ω) := by
  letI : Module S (Torus v Ω) := inferInstanceAs (Module S (M →₀ R))
  exact @Algebra.ofModule' S (Torus v Ω) _ (Torus.instRing v Ω).toSemiring
    (inferInstanceAs (Module S (M →₀ R)))
    (scalar_one_mul (S:=S) v Ω) (mul_scalar_one (S:=S) v Ω)
end
end ElementaryPositivity.QuantumTorus.Torus
end
end

end OAI
