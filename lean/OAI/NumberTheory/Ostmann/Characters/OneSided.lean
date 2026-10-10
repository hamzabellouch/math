import OAI.NumberTheory.Ostmann.Characters.Basic

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

def crtProduct {q q' : ℕ} (h : q.Coprime q')
    (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ) (n : ZMod (q*q')) : ℂ :=
  χ ((ZMod.chineseRemainder h n).1) * conj (ξ ((ZMod.chineseRemainder h n).2))

theorem crtProduct_sum_zero {q q' : ℕ} [NeZero q] [NeZero q']
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (hχ : χ ≠ 1) : ∑ n : ZMod (q*q'), crtProduct h χ ξ n = 0 := by
  unfold crtProduct
  rw [Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv
    (fun n => χ ((ZMod.chineseRemainder h n).1) * conj (ξ ((ZMod.chineseRemainder h n).2)))
    (fun z : ZMod q × ZMod q' => χ z.1 * conj (ξ z.2)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul,
    MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

theorem crtProduct_sum_affine_zero {q q' : ℕ} [NeZero q] [NeZero q']
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (hχ : χ ≠ 1) (u : (ZMod (q*q'))ˣ) (a : ZMod (q*q')) :
    ∑ n : ZMod (q*q'), crtProduct h χ ξ (↑u*n+a) = 0 := by
  calc
    _ = ∑ n : ZMod (q*q'), crtProduct h χ ξ n :=
      Fintype.sum_bijective _ ((Equiv.addRight a).bijective.comp u.mulLeft_bijective)
        _ _ (fun _ => rfl)
    _ = 0 := crtProduct_sum_zero h χ ξ hχ
end Ostmann.Characters

end

end OAI
