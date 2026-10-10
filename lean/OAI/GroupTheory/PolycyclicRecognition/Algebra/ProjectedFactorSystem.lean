import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem

namespace OAI

/-! # The factor system induced by a surjective equivariant kernel map -/

namespace PolycyclicRecognition
variable {N K Q : Type*} [Group N] [Group K] [Group Q]

def NonabelianFactorSystem.mapSurjective (S : NonabelianFactorSystem N Q)
    (p : N →* K) (hp : Function.Surjective p) (a : Q → MulAut K)
    (ha : ∀ q x, p (S.action q x) = a q (p x)) : NonabelianFactorSystem K Q where
  action := a
  factor q r := p (S.factor q r)
  action_one := by
    apply DFunLike.ext
    intro k
    obtain ⟨x, rfl⟩ := hp k
    rw [← ha, S.action_one]
    rfl
  factor_one_left q := by rw [S.factor_one_left, map_one]
  factor_one_right q := by rw [S.factor_one_right, map_one]
  action_mul q r := by
    apply DFunLike.ext
    intro k
    obtain ⟨x, rfl⟩ := hp k
    change a q (a r (p x)) = p (S.factor q r) * a (q * r) (p x) * (p (S.factor q r))⁻¹
    rw [← ha, ← ha, S.action_mul_apply, map_mul, map_mul, map_inv, ha]
  cocycle q r s := by
    have h := congrArg p (S.cocycle q r s)
    simpa only [map_mul, ha] using h

end PolycyclicRecognition

end OAI
