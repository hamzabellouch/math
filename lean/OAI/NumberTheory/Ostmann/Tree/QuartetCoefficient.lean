import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyPullback
import OAI.NumberTheory.Ostmann.Tree.QuartetMellinPullback

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

theorem twoPairRatio_inverse_square_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (lam mu y K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) :
    ‖mellin (fun z : (ZMod p)ˣ => twoPairRatioValue g h σ τ L R lam mu y (K/z^2)) ρ‖^2 ≤
      2*‖(p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)‖^2 *
        ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ⁻¹,
          ‖twoPairConvolution g h σ τ L R χ⁻¹ lam mu y‖^2 := by
  classical
  have hb := mellin_inverse_square_pullback (twoPairRatioValue g h σ τ L R lam mu y) K ρ
  simp_rw [twoPairRatio_mellin g h σ τ L R lam mu y _ hg0, norm_mul, mul_pow] at hb
  rw [← Finset.mul_sum] at hb
  simpa only [mul_assoc] using hb

end Ostmann.FiniteField

namespace Ostmann.Tree.Quartet.NodeInput
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

theorem crossFamily_coefficient_bound (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (a b : Bool) (m h k : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    ‖mellin (N.crossFamilyFunction g a b m h k) ρ‖^2 ≤
      2*‖(p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)‖^2 *
        ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ⁻¹,
          ‖twoPairConvolution (signedFunction g (parameterSign N.left a))
            (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
            (pairMode a) (pairMode b) χ⁻¹ (N.leftLambda m a*h^2) (N.rightLambda m b*k^2)
            (N.familyRoot m)‖^2 := by
  classical
  have he : N.crossFamilyFunction g a b m h k = fun z : (ZMod p)ˣ =>
      twoPairRatioValue (signedFunction g (parameterSign N.left a))
        (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
        (pairMode a) (pairMode b) (N.leftLambda m a*h^2) (N.rightLambda m b*k^2)
        (N.familyRoot m) (N.familyRatioConstant m h/z^2) := by
    funext z
    exact crossFamily_pullback_point N hcons hopp g hg0 a b m h k z
  rw [he]
  exact twoPairRatio_inverse_square_bound _ _ _ _ _ _ _ _ _ _ ρ (signedFunction_zero g hg0 _)

end Ostmann.Tree.Quartet.NodeInput
end

end OAI
