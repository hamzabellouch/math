import OAI.Algebra.AuslanderReiten.Bar.ModuleBarHomTwist
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarSuffix

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (p : AbsoluteBar.Cochain3 k R) (c : k)
variable (hp : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hp

theorem transport_suffixComparison (n : ℕ) (x : object k R M (n+3)) :
    suffixComparison k R M p n (transport k R M h e (n+3) x) =
      c • transport k R M h e n (suffixComparison k R M p n x) := by
  induction n with
  | zero => exact transport_suffix3 k R M h e p c hp x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul a x =>
      change suffixComparison k R M p (n+1)
        (h a ⊗ₜ[k] transport k R M h e (n+3) x) = _
      rw [suffixComparison_succ_tmul, ih, suffixComparison_succ_tmul, transport_tmul,
        TensorProduct.tmul_smul]

include he

theorem transportHom_suffixComparison (n : ℕ)
    (f : moduleObject k R M (n+1) →ₗ[R] M) :
    transportHom k R M h e he (n+4) (f.comp (suffixComparisonMap k R M p n)) =
      c • (transportHom k R M h e he (n+1) f).comp (suffixComparisonMap k R M p n) := by
  ext x
  change e.symm (f (suffixComparison k R M p (n+1) (transport k R M h e (n+4) x))) =
    c • e.symm (f (transport k R M h e (n+1) (suffixComparison k R M p (n+1) x)))
  erw [transport_suffixComparison k R M h e p c hp (n+1)]
  exact (congrArg e.symm ((f.restrictScalars k).map_smul c
    (transport k R M h e (n+1) (suffixComparison k R M p (n+1) x)))).trans
      (e.symm.map_smul c _)

end ArExplicit.ModuleBar

end

end OAI
